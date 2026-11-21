module formatters.page

import std.list
import std.string (Template, Hole)

record Page
    parts~List String          # the last first

export fn page n k -> p : n~Nat, k~Nat, p~Page
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
