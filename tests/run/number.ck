module number

# Decimal numbers, read and written by `std.number`: each argument read as a
# `Nat` and as an `Int`, and written back.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string
import std.number

fn nat_line b term : b~Bytes, term~Term
    match number.parse_nat b
        Some n -> terminal.write_bytes (b"nat " ++ number.render_nat n ++ b"\n") term
        None   -> terminal.write_bytes b"nat none\n" term

fn int_line b term : b~Bytes, term~Term
    match number.parse_int b
        Some n -> terminal.write_bytes (b"int " ++ number.render_int n ++ b"\n") term
        None   -> terminal.write_bytes b"int none\n" term

fn each args term : args~List String, term~Term
    match args
        []        -> ()
        a :: rest ->
            terminal.write_bytes (b"[" ++ string.bytes a ++ b"]\n") term
            nat_line (string.bytes a) term
            int_line (string.bytes a) term
            each rest term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    each args term
    terminal.write_bytes (number.render_nat 12345678901234567890123456789012 ++ b"\n") term
    terminal.write_bytes (number.render_nat 170141183460469231731687303715884105728 ++ b"\n") term
    terminal.write_bytes (number.render_int (-170141183460469231731687303715884105728) ++ b"\n") term
    Success
