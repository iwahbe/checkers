module echo

# Number the lines of standard input; `partial` because input may not end.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.files
import std.string (debug)

partial fn number n term : n~Nat, term~Term
    match terminal.read_line term
        Ok (Some l) ->
            terminal.write (debug n ++ ": ") term
            terminal.write_bytes l term
            terminal.write "\n" term
            number (n + 1) term
        Ok None     -> ()
        Err e       -> terminal.eprint_line (files.describe e) term

export partial fn main args sys -> code : args~List String, sys~System, code~ExitCode
    number 1 sys.term
    match args
        [] -> Success
        _  -> Failure (len args + 10)
