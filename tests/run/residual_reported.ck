module residual_reported

# The check that every operation on values known when compiling is computed
# then: with folding turned off (`CHECKERS_NO_FOLD=1`, which exists to test
# the check), `21 * 2` is left to run, and the check reports it as a compiler
# bug. The program doesn't run.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.hint (blackbox)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (if blackbox 0 + 21 * 2 == 42 then "no arguments" else "arguments") sys.term
    Success
