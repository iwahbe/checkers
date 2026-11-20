module instance_unit

# `()`, written so or as `Unit`, has instances as `Bool` does; one for
# tuples recurses over `(a, b)` down to `()`.

import std.system (System, ExitCode)
import std.terminal

class Size t
    fn size x -> n : x~t, n~Nat

instance Size Unit
    fn size x
        0

instance Size Bool
    fn size x
        1

instance Size (a, b) : Size a, Size b
    fn size p
        let (x, y) = p
        Size.size x + Size.size y

class Name t
    fn name x -> s : x~t, s~String

instance Name ()
    fn name x
        "unit"

export fn main args sys -> code
    let System { term } = sys
    terminal.print_line (format (size (True, (False, ())))) term
    terminal.print_line (name ()) term
    Success
