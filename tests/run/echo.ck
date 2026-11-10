module echo

# Number the lines of standard input; `partial` because input may not end.

import system (System, ExitCode)
import terminal (Term)

partial fn number n term : n~Nat, term~Term
    match terminal.read_line term
        None   -> ()
        Some l ->
            terminal.print_line (format n ++ ": " ++ l) term
            number (n + 1) term

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    number 1 sys.term
    match args
        [] -> Success
        _  -> Failure (len args + 10)
