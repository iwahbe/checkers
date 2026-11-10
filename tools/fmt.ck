# fmt.ck — `checkers fmt` (SPEC §15.4): format files in place, check that
# they are formatted, or format standard input.

module fmt

import system (ExitCode)
import terminal (Term)
import files (Fs, Entry)
import string
import bytes
import ck.format as formatter
import ck.syntax (SyntaxError)

export let USAGE = string.concat [
    "usage: checkers fmt [--check] [PATH]...\n",
    "       checkers fmt -\n\n",
    "Formats each .ck file under each PATH (default: the current directory) in place.\n",
    "--check changes nothing: it lists the files that would change, and fails if\n",
    "there are any. `-` formats standard input to standard output."]

fn ends_with s suffix : s~String, suffix~String
    let b = string.bytes s
    let x = string.bytes suffix
    len x <= len b and bytes.matches_at b (len b - len x) x

fn hidden name : name~String
    let b = string.bytes name
    len b > 1 and b[0] == '.'

fn join_path dir name -> p : dir~String, name~String, p~String
    if dir == "." then name else dir ++ "/" ++ name

# The `.ck` files under `path`: itself, if it names one.
partial fn ck_files path fs -> r : path~String, fs~Fs, r~List String
    if ends_with path ".ck"
        [path]
    else
        match files.list path fs
            Ok es -> entries path es fs
            Err _ -> [path]

partial fn entries dir es fs -> r : dir~String, es~List Entry, fs~Fs, r~List String
    match es
        [] -> []
        e :: rest ->
            let here = if e.dir and not (hidden e.name)
                ck_files (join_path dir e.name) fs
            else if not e.dir and ends_with e.name ".ck"
                [join_path dir e.name]
            else
                []
            here ++ entries dir rest fs

fn describe where e -> s : where~String, e~SyntaxError, s~String
    where ++ ":" ++ format e.line ++ ":" ++ format (e.col + 1) ++ ": " ++ e.message

# What happened to the files so far.
record Tally
    failed~Bool
    changed~Bool

partial fn each paths verify fs term t -> r : paths~List String, verify~Bool, fs~Fs, term~Term, t~Tally, r~Tally
    match paths
        [] -> t
        p :: rest -> each rest verify fs term (one p verify fs term t)

partial fn one path verify fs term t -> r : path~String, verify~Bool, fs~Fs, term~Term, t~Tally, r~Tally
    match files.read path fs
        Err e ->
            terminal.eprint_line (path ++ ": " ++ files.describe e) term
            Tally True t.changed
        Ok src ->
            match formatter.format src
                Err e ->
                    terminal.eprint_line (describe path e) term
                    Tally True t.changed
                Ok out ->
                    if out == src
                        t
                    else if verify
                        terminal.print_line path term
                        Tally t.failed True
                    else
                        match files.write path out fs
                            Ok _ -> Tally t.failed True
                            Err e ->
                                terminal.eprint_line (path ++ ": " ++ files.describe e) term
                                Tally True t.changed

fn stdin term -> code : term~Term, code~ExitCode
    match terminal.read_all term
        Err e ->
            terminal.eprint_line ("<stdin>: " ++ files.describe e) term
            Failure 1
        Ok src ->
            match formatter.format src
                Ok out ->
                    terminal.write_bytes out term
                    Success
                Err e ->
                    terminal.eprint_line (describe "<stdin>" e) term
                    Failure 1

partial fn collect paths fs -> r : paths~List String, fs~Fs, r~List String
    match paths
        [] -> []
        p :: rest -> ck_files p fs ++ collect rest fs

# `checkers fmt ARGS`.
export partial fn run args term fs -> code : args~List String, term~Term, fs~Fs, code~ExitCode
    match args
        ["-"] -> stdin term
        ["--help"] ->
            terminal.print_line USAGE term
            Success
        "--check" :: paths -> files_mode paths True term fs
        paths -> files_mode paths False term fs

# A flag among the paths: in the wrong place.
fn flagged paths : paths~List String
    match paths
        [] -> False
        p :: rest -> p == "-" or p == "--check" or flagged rest

partial fn files_mode paths verify term fs -> code : paths~List String, verify~Bool, term~Term, fs~Fs, code~ExitCode
    if flagged paths
        terminal.eprint_line USAGE term
        Failure 2
    else
        let roots = if paths == [] then ["."] else paths
        let t = each (collect roots fs) verify fs term (Tally False False)
        if t.failed or (verify and t.changed) then Failure 1 else Success
