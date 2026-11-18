module big_literals

# Number literals of any size: `Int` and `Nat` have no fixed size.

import std.system (System, ExitCode)
import std.terminal (Term)

fn pow b e -> r : b~Int, e~Nat, r~Int
    decreasing e
    match e
        0 -> 1
        _ -> b * pow b (e - 1)

# 2^127, one past the largest 128-bit signed integer.
fn value -> n : n~Int
    170141183460469231731687303715884105728

# Proved with the literal itself.
fn above -> n : n~Int, n > 170141183460469231731687303715884105727
    170141183460469231731687303715884105728

fn name n -> s : n~Int, s~String
    match n
        -170141183460469231731687303715884105729                      -> "below"
        170141183460469231731687303715884105728                       -> "2^127"
        1606938044258990275541962092341162602522202993782792835301376 -> "2^200"
        _                                                             -> "other"

check value == pow 2 127
check 0x8000_0000_0000_0000_0000_0000_0000_0000 == value
check 1606938044258990275541962092341162602522202993782792835301376 == pow 2 200
check 170141183460469231731687303715884105727 + 1 == value
check -170141183460469231731687303715884105728 - 1 == -value - 1
check value * value / value == value

fn line s term : s~String, term~Term
    terminal.print_line s term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    line (format value) term
    line (format above) term
    line (format (-170141183460469231731687303715884105728)) term
    line (format 0x1_0000_0000_0000_0000_0000_0000_0000_0000) term
    line (name (pow 2 127)) term
    line (name (pow 2 200)) term
    line (name (-value - 1)) term
    line (name 3) term
    Success
