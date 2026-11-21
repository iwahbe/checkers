# run.ck — runs CommonMark's spec examples (spec.json) through std.markdown
# and prints each one whose HTML isn't the spec's, then how many pass.
# `run spec.json N` prints example N whether it passes or not.

module run

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.files
import std.json (Json, Str, Num, Arr, Obj)
import std.decimal
import std.markdown
import std.list
import std.string
import std.string (debug)

record Example
    number~String
    section~String
    markdown~String
    html~String

fn field fs name -> r : fs~List (String, Json), name~String, r~String
    match fs
        (k, Str s) :: rest -> if k == name then s else field rest name
        (k, Num n) :: rest -> if k == name then decimal.render n else field rest name
        _ :: rest          -> field rest name
        []                 -> ""

fn example v -> r : v~Json, r~Example
    match v
        Obj fs -> Example (field fs "example") (field fs "section") (field fs "markdown") (field fs "html")
        _      -> Example "" "" "" ""

# The examples that fail (or example `only`), printed; how many fail.
fn report es only term -> r : es~List Example, only~String, term~Term, r~Nat
    match es
        e :: rest ->
            let got = markdown.to_html (markdown.parse e.markdown)
            let shown = if only == "" then got != e.html else only == e.number
            if shown
                terminal.print_line (string.concat ["── example ", e.number, " (", e.section, ")\n", e.markdown,
                                                    "--- expected\n", e.html, "--- got\n", got]) term
            else
                ()
            (if got != e.html then 1 else 0) + report rest only term
        []        -> 0

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term, fs } = sys
    let (path, only) = match args
        [p, n] -> (p, n)
        [p]    -> (p, "")
        _      -> ("spec.json", "")
    match files.read path fs
        Err e  ->
            terminal.eprint_line (files.describe e) term
            Failure 1
        Ok src ->
            match json.parse src
                Ok (Arr items) ->
                    let failed = report (list.map example items) only term
                    let total = list.length items
                    let passed = if total >= failed then total - failed else 0
                    terminal.print_line (debug passed ++ " of " ++ debug total ++ " examples pass") term
                    if failed == 0 then Success else Failure 1
                _              ->
                    terminal.eprint_line (path ++ ": not a JSON array") term
                    Failure 1
