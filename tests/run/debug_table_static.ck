module debug_table_static

# The table of hand-written `Debug` instances the runtime shows values with
# is static data, laid out when the program is compiled: nothing builds it
# when the program starts. `Secret`'s own `debug` shows inside a list.

import std.system (System, ExitCode)
import std.string (Debug, debug)
import std.terminal (Term)
import std.hint (blackbox)

record Secret
    code~Int

instance Debug Secret
    fn debug s
        "Secret <hidden>"

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line (debug [Secret (blackbox 7)]) sys.term
    Success
