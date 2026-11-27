# An abstract type shows importers its name only (§6, #637): they can't
# build one, match on it or read its fields, only use what its module
# exports.
module abstract_sealed

import std.list
import sealed.tx (Tx, State, begin, commit)

fn build -> t : t~Tx
    Tx []

fn take_apart -> n : n~Nat
    match begin
        Tx log -> list.length log

fn read -> n : n~Nat
    list.length begin.log

fn state s -> n : s~State, n~Nat
    match s
        Fresh -> 0
        _     -> 1

fn through_api -> n : n~Nat
    commit begin
