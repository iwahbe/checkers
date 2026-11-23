module parse_decimal_edges

# Signs, exponents, leading zeros and points at the edges of the number
# grammar, from bytes and from lists of bytes.

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

fn each xs term -> r : xs~List Bytes, term~Term, r~Unit
    match xs
        []        -> ()
        b :: rest ->
            terminal.print_line (shown (Parsable.parse b Decimal Int)) term
            terminal.print_line (shown (Parsable.parse (array.to_list b) Decimal Int)) term
            each rest term

export fn main args sys -> code
    let System { term } = sys
    each [b"1e+5", b"1e+-5", b"1e-+5", b"1e--5", b"1e-x", b"1e+", b"1e-", b"1e", b"1E05", b"1e-007", b"-0", b"-01", b"0.0",
          b"0.", b"0e5", b"00", b"-", b"-x", b"+1", b".5", b"1.5e+3x", b"12.034e-2", b"9007199254740993e400",
          b"-0.000e+0", b"123456789012345678901234567890", b"1.e5", b"1e5.5", b"e5", b"--1", b"1-", b"0x10"] term
    Success
