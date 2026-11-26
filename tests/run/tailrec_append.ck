# `++` after a recursive call, with a literal or variable on the right (§14):
# the pieces are appended in the order the recursion gives, each copied once,
# so strings, bytes, arrays and lists of 100 000 pieces take linear time.
# Every result is the one the recursion gives.
module tailrec_append

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.array
import std.string (debug)

fn line s term : s~String, term~Term
    terminal.print_line s term

fn by_atom n -> r : n~Nat, r~String
    if n == 0 then "" else by_atom (n - 1) ++ "x"

# A base case that isn't empty, two pieces, and a call with nothing after it.
fn by_parity n s -> r : n~Nat, s~String, r~String
    if n == 0
        "<"
    else if n % 2 == 0
        by_parity (n - 1) s ++ s
    else if n == 5
        by_parity (n - 1) s
    else
        by_parity (n - 1) s ++ "."

# The base case is the piece itself.
fn by_bytes n piece -> r : n~Nat, piece~Bytes, r~Bytes
    if n == 0 then piece else by_bytes (n - 1) piece ++ piece

# Elements the base case's layout can't hold.
fn by_array n base piece -> r : n~Nat, base~Array Int, piece~Array Int, r~Array Int
    if n == 0 then base else by_array (n - 1) base piece ++ piece

fn by_strings n piece -> r : n~Nat, piece~Array String, r~Array String
    if n == 0 then array.from_list [] else by_strings (n - 1) piece ++ piece

fn by_list n piece -> r : n~Nat, piece~List Nat, r~List Nat
    if n == 0 then [0] else by_list (n - 1) piece ++ piece

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    line (by_atom 5) term
    line (by_parity 8 "ab") term
    line (debug (by_bytes 3 (string.bytes "ab"))) term
    line (debug (array.to_list (by_array 3 (array.from_list [-1]) (array.from_list [300, 7])))) term
    line (debug (array.to_list (by_strings 2 (array.from_list ["p", "q"])))) term
    line (debug (by_list 3 [1, 2])) term
    let n = 100000
    line (debug (len (by_atom n).bytes)) term
    line (debug (len (by_parity n "ab").bytes)) term
    line (debug (len (by_bytes n (string.bytes "ab")))) term
    let a = by_array n (array.from_list [-1]) (array.from_list [300, 7])
    line (debug (len a) ++ " " ++ (if 2 * n < len a then debug a[0] ++ " " ++ debug a[2 * n] else "?")) term
    line (debug (len (by_strings n (array.from_list ["p", "q"])))) term
    line (debug (len (by_list n [1, 2]))) term
    Success
