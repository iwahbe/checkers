module unboxed

# Benchmark (§14): functions whose results their callers take apart at once.
# Each mode prints one number.
#
#   unboxed grammar  numbers and commas read from 3 MB of bytes by readers in
#                    `std.parse`'s shape, each giving `Ok (value, rest)` or
#                    `Err`, calling each other directly
#   unboxed record   a function giving a record, and one giving one of three
#                    constructors, each taken apart by its caller
#   unboxed nested   results of nested constructors: `Some (Ok n, k)`

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)
import std.bytes

# ── Grammar ──

# `n` copies of a line of numbers.
fn input n acc -> r : n~Nat, acc~List Bytes, r~Bytes
    decreasing n
    if n == 0 then bytes.concat acc else input (n - 1) (b"12345,678,9,31415,27," :: acc)

# The digits at the front of `xs`, after `acc`.
fn digits xs acc -> r : xs~Bytes, acc~Int, r~Result (Int, Bytes) Unit
    decreasing len xs
    match xs
        b :: rest -> if b >= '0' and b <= '9' then digits rest (acc * 10 + (b - '0')) else Ok (acc, xs)
        []        -> Ok (acc, xs)

# A number: one digit or more.
fn number xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit
    match xs
        b :: rest -> if b >= '0' and b <= '9' then digits rest (b - '0') else Err ()
        []        -> Err ()

fn comma xs -> r : xs~Bytes, r~Result (Unit, Bytes) Unit
    match xs
        b :: rest -> if b == ',' then Ok ((), rest) else Err ()
        []        -> Err ()

# A number and its comma.
fn item xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit
    match number xs
        Err e        -> Err e
        Ok (n, rest) ->
            match comma rest
                Err e         -> Err e
                Ok (_, after) -> Ok (n, after)

# The sum of the items in `xs`, after `total`; at most `fuel` of them.
fn items xs total fuel -> r : xs~Bytes, total~Int, fuel~Nat, r~Int
    decreasing fuel
    if fuel == 0
        total
    else
        match item xs
            Err _         -> total
            Ok (n, after) -> items after (total + n) (fuel - 1)

fn grammar -> r : r~Int
    let src = input 150000 []
    items src 0 (len src)

# ── Records and choices ──

record Step
    value~Int
    seed~Int

# A pseudo-random number below 1000, and the next seed.
fn next seed -> s : seed~Int, s~Step
    let x = (seed * 1103515245 + 12345) % 2147483648
    Step (x % 1000) x

enum Move
    Up n   : n~Int
    Down n : n~Int
    Stay

fn move v -> m : v~Int, m~Move
    if v < 300 then Up v else if v < 600 then Down (v - 300) else Stay

# Where `n` random moves from `at` end.
fn walk n seed at -> r : n~Nat, seed~Int, at~Int, r~Int
    decreasing n
    if n == 0
        at
    else
        match next seed
            Step v s ->
                match move v
                    Up k   -> walk (n - 1) s (at + k)
                    Down k -> walk (n - 1) s (at - k)
                    Stay   -> walk (n - 1) s at

fn record_walk -> r : r~Int
    walk 3000000 42 0

# ── Nested constructors ──

# The next of `n`'s Collatz sequence, and the count after it.
fn split n k -> r : n~Int, k~Int, r~Option (Result Int Int, Int)
    if n <= 1 then None else if n % 2 == 0 then Some (Ok (n / 2), k + 1) else Some (Err (3 * n + 1), k + 1)

# The steps from `n` to 1, after `k`.
fn steps n k fuel -> r : n~Int, k~Int, fuel~Nat, r~Int
    decreasing fuel
    if fuel == 0
        k
    else
        match split n k
            None            -> k
            Some (Ok m, j)  -> steps m j (fuel - 1)
            Some (Err m, j) -> steps m j (fuel - 1)

# The steps from each of `1 .. n`, added to `total`.
fn all_steps n total -> r : n~Nat, total~Int, r~Int
    decreasing n
    if n == 0 then total else all_steps (n - 1) (total + steps n 0 1000)

fn nested -> r : r~Int
    all_steps 300000 0

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let r = match args
        ["grammar"] -> grammar
        ["record"]  -> record_walk
        ["nested"]  -> nested
        _           -> -1
    terminal.print_line (debug r) sys.term
    if r < 0 then Failure 2 else Success
