module arith

# Arbitrary-precision numbers (D6) and Euclidean division (§13.2).

import std.system (System, ExitCode)
import std.terminal (Term)

fn pow b e -> r : b~Int, e~Nat, r~Int
    decreasing e
    match e
        0 -> 1
        _ -> b * pow b (e - 1)

fn line s term : s~String, term~Term
    terminal.print_line s term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    line (format (pow 2 200)) term
    line (format (pow 2 200 - pow 2 200 + 1)) term
    line (format (pow (-3) 41)) term
    line (format (-7 / 2) ++ " " ++ format (-7 % 2)) term
    line (format (7 / 2) ++ " " ++ format (7 % 2)) term
    line (format (pow 10 30 > pow 10 29)) term
    Success
