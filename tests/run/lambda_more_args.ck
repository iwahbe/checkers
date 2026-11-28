module lambda_more_args

# A lambda applied to more arguments than it takes, in a specialized copy:
# each argument is the one passed.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.list

fn apply3 f x y z -> r : f~(Int -> Int -> Int -> Int), x~Int, y~Int, z~Int, r~Int
    f x y z

fn digits a b c -> r : a~Int, b~Int, c~Int, r~Int
    a * 100 + b * 10 + c

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let n = list.length args
    terminal.print_line (debug (apply3 (\a -> digits a) (n + 1) (n + 2) (n + 3))) sys.term
    Success
