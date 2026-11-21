module computed_elem

# A type argument computed from a local variable (D178): its layout isn't
# known where the call is compiled, so the value is stored as a word.

import std.array
import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

fn single x -> xs : x~a, xs~Array a
    array.from_list [x]

fn boxed b x -> xs : b~Bool, x~(if b then U8 else Int), xs~Array (List (if b then U8 else Int))
    single [x]

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (len (boxed False 3000))) sys.term
    terminal.print_line (debug (len (boxed True 3))) sys.term
    Success
