module template_errors

import std.list
import std.string (Template, Hole)

record Page
    parts~List String

enum Mode
    Raw

enum Style
    Bold

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
        Page (x :: p.parts)

record Plain
    parts~List String

fn plain n k -> p : n~Nat, k~Nat, p~Plain
    Plain []

instance Template Plain
    type Result = String
    fn text p str
        Plain (str :: p.parts)
    fn finish p
        string.concat p.parts

instance Hole Plain String
    fn hole p x os
        Plain (x :: p.parts)

instance Hole Plain Int
    fn hole p x os
        Plain (format x :: p.parts)

fn count n k -> c : n~Nat, k~Nat, c~Int
    k

fn no_instance count : count~Nat
    page"<p>{count}</p>"

fn wrong_option name : name~String
    page"<p>{name | Bold}</p>"

fn no_template x : x~String
    count"a{x}"

fn never_known
    let item = page"<li>{}</li>"
    "done"

fn neither flag : flag~Bool
    plain"{flag}"

fn divided d : d~Int
    plain"{10 / d}"
