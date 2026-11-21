module template

# Templates: a formatter that escapes HTML and takes only strings, with
# named and positional holes and options; one whose result isn't a
# string; one configured by partial application; and the sizes a tag is
# given, with positional holes of different types.

import std.system (System, ExitCode)
import std.terminal
import std.list
import std.string (Template, Hole, debug)
import std.html

record Page
    parts~List String          # the last first

enum Mode
    Raw                        # the value as it is

fn page n k -> p : n~Nat, k~Nat, p~Page
    Page []

instance Template Page
    type Result = String
    fn text p str
        Page (str :: p.parts)
    fn finish p
        string.concat (list.reverse p.parts)

instance Hole Page String
    type Options = Mode
    fn hole p x os
        Page ((if list.contains os Raw then x else html.escape x) :: p.parts)

# A query: its text, with a placeholder for each value, and the values.
record Query
    sql~String
    params~List Int

enum Dialect
    Numbered                   # `$1`, `$2`, …
    Marks                      # `?`

record Building
    dialect~Dialect
    sql~String
    params~List Int            # the last first

fn query dialect n k -> b : dialect~Dialect, n~Nat, k~Nat, b~Building
    Building dialect "" []

instance Template Building
    type Result = Query
    fn text b str
        Building b.dialect (b.sql ++ str) b.params
    fn finish b
        Query b.sql (list.reverse b.params)

instance Hole Building Int
    fn hole b x os
        let mark = match b.dialect
            Numbered -> "$" ++ debug (list.length b.params + 1)
            Marks    -> "?"
        Building b.dialect (b.sql ++ mark) (x :: b.params)

# The sizes the tag was given.
record Sizes
    bytes~Nat
    holes~Nat

fn sizes n k -> s : n~Nat, k~Nat, s~Sizes
    Sizes n k

instance Template Sizes
    type Result = (Nat, Nat)
    fn text s str
        s
    fn finish s
        (s.bytes, s.holes)

instance Hole Sizes a
    fn hole s x os
        s

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    let name = "<Ann>"
    let body = "<b>hi</b>"
    terminal.print_line page"<p>{name}</p>{body | Raw}" t
    terminal.print_line (page"<li>{}</li>" name) t
    let item = page"<li>{| Raw}</li>"
    terminal.print_line (item body) t
    terminal.print_line page"{{{name}}}" t
    let q = query Numbered
    let id = 7
    let r = q"select * from t where id = {id} and n < {id + 1}"
    terminal.print_line r.sql t
    terminal.print_line (debug r.params) t
    let m = query Marks
    terminal.print_line m"id = {id}".sql t
    terminal.print_line (debug sizes"ab{1}c\u{e9}{{{2}") t
    terminal.print_line (debug sizes"") t
    terminal.print_line (debug (sizes"{} and {}" "a" 2)) t
    Success
