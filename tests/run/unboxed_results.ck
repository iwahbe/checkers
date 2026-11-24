module unboxed_results

# Results returned as their parts (§14): functions whose every result is a
# constructor or tuple they build, taken apart by their callers. Each line
# is what the value built and taken apart gives: sums with nested tuples,
# literal results, records, a tuple whose last component is a tuple, a
# value also needed whole, a function used as a closure, functions calling
# each other in tail position, a failure, and arguments with effects.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

fn digit xs -> r : xs~List Int, r~Result (Int, List Int) String
    match xs
        []        -> Err "end"
        x :: rest -> if x < 10 then Ok (x, rest) else Err ("not a digit: " ++ debug x)

fn by_sum xs -> s : xs~List Int, s~String
    match digit xs
        Err e        -> "error " ++ e
        Ok (d, rest) ->
            match digit rest
                Err e         -> "one " ++ debug d ++ ", then " ++ e
                Ok (d2, more) -> "two " ++ debug (d * 10 + d2) ++ ", left " ++ debug more

record Step
    value~Int
    next~Int

fn step n -> s : n~Int, s~Step
    Step (n * 2) (n + 1)

fn by_field n -> r : n~Int, r~Int
    let s = step n
    s.value + s.next

# `b` is a tuple: the result is `(a, b0, b1)` at run time.
fn wrap a b -> r : a~Int, b~(Int, Int), r~(Int, (Int, Int))
    (a, b)

fn by_three a -> s : a~Int, s~String
    let (x, y, z) = wrap a (a + 1, a + 2)
    debug x ++ " " ++ debug y ++ " " ++ debug z

fn by_rest a -> s : a~Int, s~String
    let (x, yz) = wrap a (a + 1, a + 2)
    debug x ++ " " ++ debug yz

fn half n -> r : n~Int, r~Option (Int, Int)
    if n % 2 == 0 then Some (n / 2, n % 7) else None

# Taken apart, and also kept whole.
fn by_whole n -> s : n~Int, s~String
    let r = half n
    match r
        Some (h, _) -> debug h ++ " of " ++ debug r
        None        -> "odd " ++ debug r

fn apply f x -> r : f~(Int -> Option (Int, Int)), x~Int, r~Option (Int, Int)
    f x

fn by_closure n -> s : n~Int, s~String
    match apply half n
        Some (h, m) -> debug h ++ " " ++ debug m
        None        -> "none"

# Calling each other in tail position: one layout.
fn even_steps n k -> r : n~Nat, k~Int, r~Result (Int, Int) Int
    decreasing n
    if n == 0 then Ok (k, 0) else odd_steps (n - 1) (k + 1)

fn odd_steps n k -> r : n~Nat, k~Int, r~Result (Int, Int) Int
    decreasing n
    if n == 0 then Err k else even_steps (n - 1) (k + 2)

fn by_steps n -> s : n~Nat, s~String
    match even_steps n 0
        Ok (k, z) -> "even " ++ debug k ++ " " ++ debug z
        Err k     -> "odd " ++ debug k

fn third xs -> r : xs~List Int, r~Option (Int, Int)
    match xs
        [a, b, c] -> if c == 0 then Some (a / c, b) else Some (a, b + c)
        _         -> None

fn by_failure xs -> s : xs~List Int, s~String
    match third xs
        Some (a, b) -> debug a ++ " " ++ debug b
        None        -> "none"

fn say s n term -> r : s~String, n~Int, term~Term, r~Int
    terminal.print_line s term
    n

fn order a b -> r : a~Int, b~Int, r~Option (Int, Int)
    if a > b then Some (a, b) else Some (b, a)

fn line s term : s~String, term~Term
    terminal.print_line s term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    line (by_sum [1, 2, 3]) term
    line (by_sum [4]) term
    line (by_sum [12]) term
    line (by_sum []) term
    line (debug (by_field 5)) term
    line (by_three 1) term
    line (by_rest 1) term
    line (by_whole 8) term
    line (by_whole 7) term
    line (by_closure 10) term
    line (by_closure 11) term
    line (by_steps 1000001) term
    line (by_steps 1000000) term
    line (by_failure [1, 2]) term
    line (by_failure [1, 2, 3]) term
    let t = match order (say "a" 1 term) (say "b" 2 term)
        Some (x, y) -> debug x ++ " " ++ debug y
        None        -> "none"
    line t term
    line (by_failure [1, 2, 0]) term
    Success
