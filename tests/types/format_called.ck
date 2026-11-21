module format_called

# A template's tag called as a function, outside a template: any function
# whose result has a `Template` instance, `format` or a program's own. A
# type error at the call, or at its first argument, says it is a tag.

import std.list
import std.string (Template, Hole, format)

record Page
    parts~List String

fn page n k -> p : n~Nat, k~Nat, p~Page
    Page []

instance Template Page
    type Result = String
    fn text p str
        Page (str :: p.parts)
    fn finish p
        string.concat (list.reverse p.parts)

instance Hole Page String
    fn hole p x os
        Page (x :: p.parts)

fn called n -> s : n~Nat, s~String
    format (n + 1)

fn of_string name -> s : name~String, s~String
    format name

fn own_tag name -> s : name~String, s~String
    page name
