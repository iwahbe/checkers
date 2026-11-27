module late_specialized

# A call is specialized on an argument known only once other code is
# folded, as on a literal: both calls of `scale` call the copy for `k == 3`.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)
import std.list
import std.hint (blackbox)

fn scale k x -> r : k~Int, x~Int, r~Int
    if k == 0 then x else x * k + k * k - x + 1

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug (scale 3 (blackbox 10))) sys.term
    terminal.print_line (debug (scale (list.length [1, 2, 3]) (blackbox 10))) sys.term
    Success
