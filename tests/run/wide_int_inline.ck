# Numbers within 128 bits never reach the runtime's arithmetic: each
# operation below, on small integers that overflow a word or on two-word
# numbers, is computed in compiled code, and its result is a small integer
# again where it fits. (A test runs this program with the runtime's
# arithmetic counted.)
module wide_int_inline

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.string (debug)

fn line s term : s~String, term~Term
    terminal.print_line s term

fn quotient x y -> r : x~Int, y~Int, y != 0, r~Int
    x / y

fn remainder x y -> r : x~Int, y~Int, y != 0, r~Int
    x % y

fn ops x y -> s : x~Int, y~Int, y != 0, s~String
    let sums = debug (x + y) ++ " " ++ debug (x - y) ++ " " ++ debug (x * y) ++ " " ++ debug (-x)
    let order = debug (x < y) ++ " " ++ debug (x <= y) ++ " " ++ debug (x == y) ++ " " ++ debug (x != y)
    let divs = debug (x / y) ++ " " ++ debug (x % y) ++ " " ++ debug (quotient x y) ++ " " ++ debug (remainder x y)
    sums ++ " | " ++ order ++ " | " ++ divs

fn down a b -> r : a~Nat, b~Nat, a >= b, r~Nat
    a - b

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    # Known only when the program runs (`n` is 0), or the operations would be
    # computed when compiling.
    let n = len args
    let big = n + 1000000000000000000000000000000
    line (ops (n + 4611686018427387903) 2) term
    line (ops (n - 4611686018427387904) (-1)) term
    line (ops big 10) term
    line (ops (-big) 7) term
    line (ops (n + 9223372036854775808) (-9223372036854775809)) term
    line (ops (n - 4611686018427387905) (-4611686018427387905)) term
    line (debug (down big (big - 5)) ++ " " ++ debug (down (n + 9223372036854775808) 4611686018427387904)) term
    Success
