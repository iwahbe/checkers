module parse_decimal

# Numbers read from the front of bytes and of lists of bytes, and how many
# bytes are left after each.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.array
import std.decimal (Decimal, DecimalError)
import std.parse (Parsable)
import std.string (debug)

fn shown r -> t : Seq s, r~Result (Decimal, s) DecimalError, t~String
    match r
        Ok (d, rest) -> decimal.render d ++ ", " ++ debug (Seq.size rest) ++ " left"
        Err e        -> debug e

fn both b term -> r : b~Bytes, term~Term, r~Unit
    terminal.print_line (shown (Parsable.parse b Decimal)) term
    terminal.print_line (shown (Parsable.parse (array.to_list b) Decimal)) term

export fn main args sys -> code
    let System { term } = sys
    both b"12.5" term
    both b"-0.001x" term
    both b"1e30" term
    both b"-12.50e-3]" term
    both b"1E+2," term
    both b"1.x" term
    both b"012" term
    both b"7e" term
    both b"-" term
    both b"x" term
    both b"" term
    Success
