module known_instance

# A class's function at a known instance, called directly (§14): instances
# without and with type parameters, with a context, of a class over a type
# constructor, with a class's type, and one that shows values of its type
# parameter; each gives what the instance's function gives, at run time
# and in a `check`.

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug)

class Size a
    fn size x -> n : x~a, n~Int

instance Size Bool
    fn size b
        if b then 1 else 0

instance Size (List a) : Size a
    fn size xs
        match xs
            []        -> 0
            x :: rest -> Size.size x + size rest

instance Size (Option a)
    fn size o
        match o
            None   -> 0
            Some _ -> 1

record Box a
    value~a

class Describe a
    fn describe x -> s : x~a, s~String

instance Describe (Box a)
    fn describe b
        "Box " ++ debug b.value

class Packed a
    type Elem
    fn elem x -> e : x~a, e~Elem

instance Packed (List a)
    type Elem = U8
    fn elem xs
        200

fn boxed x -> s : x~a, s~String
    describe (Box x)

check size [[True], [False, True]] == 2 and describe (Box 3) == "Box 3"

fn bools xs -> n : xs~List (List Bool), n~Int
    size xs

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    terminal.print_line (debug (size True)) t
    terminal.print_line (debug (size [True, False, True])) t
    terminal.print_line (debug (bools [[True], [], [True, True]])) t
    terminal.print_line (debug (size (Some 5))) t
    terminal.print_line (debug (fmap (\x -> x * 2) [1, 2, 3])) t
    terminal.print_line (describe (Box [1, 2])) t
    terminal.print_line (boxed (Some "x")) t
    let row = array.repeat 3 (Packed.elem [True])
    terminal.print_line (debug row) t
    terminal.print_line (debug (array.to_list row)) t
    Success
