# format.ck — building strings with holes: `format"{name} is {age}"`.
#
# The prelude's `format`, glued to a string, is this module's formatter, so
# `format"…"` needs no import. A hole may hold a value of any type, rendered
# as `format x` renders it: a string as itself, other values as they would
# be written in source.
module std.format

import std.prelude
import std.list
import std.string

# A string being built: its pieces so far, the last first.
export abstract record Format
    parts~List String

# A new formatter, for `format"…"`; it doesn't need the sizes it is given.
export fn format n k -> f : n~Nat, k~Nat, f~Format
    Format []

instance Template Format
    type Result = String
    fn text f s
        Format (s :: f.parts)
    fn finish f
        string.concat (list.reverse f.parts)

instance Hole Format a
    fn hole f x os
        Format (prelude.format x :: f.parts)
