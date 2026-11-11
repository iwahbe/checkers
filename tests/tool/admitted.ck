# A program relying on an `admit`: `checkers build --release` refuses it (§7.4).
module admitted

import std.system (System, ExitCode)

fn double n -> m : n~Nat, m~Nat, m == n + n
    n + n

lemma double_even n : n~Nat
    ensures double n >= n
    proof
        admit

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    have double_even 3
    Success
