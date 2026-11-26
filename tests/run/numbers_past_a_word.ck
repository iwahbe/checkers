# Numbers past what a word holds keep their values through arithmetic,
# comparison and equality, as they grow past 128 bits and come back (§14).
module numbers_past_a_word

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.string (debug)

fn line s term : s~String, term~Term
    terminal.print_line s term

# `x` times 2, `k` times, each step shown.
fn up x k term -> r : x~Int, k~Nat, term~Term, r~Int
    decreasing k
    if k == 0
        x
    else
        line (debug (x * 2)) term
        up (x * 2) (k - 1) term

# `x` divided by 2, `k` times, each step shown with its remainder by 7.
fn down x k term -> r : x~Int, k~Nat, term~Term, r~Int
    decreasing k
    if k == 0
        x
    else
        line (debug (x / 2) ++ " % 7 = " ++ debug (x / 2 % 7)) term
        down (x / 2) (k - 1) term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    # 2^61 to 2^63, past a word; 2^126 to 2^129, past 128 bits.
    let a = up 1152921504606846976 2 term
    let b = up 42535295865117307932921825928971026432 3 term
    let c = down b 3 term
    line (debug (c == 42535295865117307932921825928971026432)) term
    line (debug (down (0 - a) 2 term)) term
    # The edges of 128 bits, crossed by one.
    let top = 170141183460469231731687303715884105727
    let bottom = -170141183460469231731687303715884105728
    line (debug (top + 1) ++ " " ++ debug (top + 1 - 1 == top)) term
    line (debug (bottom - 1) ++ " " ++ debug (bottom - 1 + 1 == bottom)) term
    line (debug (0 - bottom) ++ " " ++ debug (bottom / (-1)) ++ " " ++ debug (bottom % 10)) term
    line (debug (a < b) ++ " " ++ debug (0 - b < 0 - a) ++ " " ++ debug (top < top + 1)) term
    line (debug [a, b * b, a - a]) term
    Success
