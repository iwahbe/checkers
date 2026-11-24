module fn_copies

# Functions called with a known function (a definition, a lambda, a
# partial application) run as copies in which calls of it are direct
# (§14): the results are those of calling it through a closure.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (debug)

fn digit xs -> r : xs~List Int, r~Result (Int, List Int) Unit
    match xs
        x :: rest -> if x < 10 then Ok (x, rest) else Err ()
        []        -> Err ()

fn below n xs -> r : n~Int, xs~List Int, r~Result (Int, List Int) Unit
    match xs
        x :: rest -> if x < n then Ok (x, rest) else Err ()
        []        -> Err ()

fn twice p xs -> r : p~(List Int -> Result (Int, List Int) Unit), xs~List Int, r~Int
    match p xs
        Err _        -> 0
        Ok (a, rest) ->
            match p rest
                Err _     -> a
                Ok (b, _) -> a * 10 + b

# Passed on to itself.
fn count p xs -> r : p~(List Int -> Result (Int, List Int) Unit), xs~List Int, r~Int
    decreasing len xs
    match xs
        []     -> 0
        _ :: _ ->
            match p xs
                Err _       -> 0
                Ok (_, mid) -> if len mid < len xs then 1 + count p mid else 0

# A different function at each call: copies stop at a bound.
fn grow n f x -> r : n~Nat, f~(Int -> Int), x~Int, r~Int
    decreasing n
    if n == 0 then f x else grow (n - 1) (\y -> f (f y)) x

fn by_index body n -> r : n~Nat, body~(m~Nat -> (self~(k~Nat -> s~Int, k < m) -> b~Int)), r~Int
    decreasing n
    body n (\k -> by_index body k)

fn say s n term -> r : s~String, n~Int, term~Term, r~Int
    terminal.print_line s term
    n

fn between a f b -> r : a~Int, f~(Int -> Int), b~Int, r~Int
    f a + f b

fn line s term : s~String, term~Term
    terminal.print_line s term

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    let n = len args + 5
    line (debug (twice digit [1, 2, 3])) term
    line (debug (twice digit [12])) term
    line (debug (twice (\xs -> below n xs) [4, 6])) term
    line (debug (twice (below n) [3, 4])) term
    line (debug (count digit [1, 2, 3, 40, 5])) term
    line (debug (count (\xs -> below n xs) [1, 2, 3, 4])) term
    line (debug (grow 3 (\y -> y + n) 0)) term
    line (debug (grow 30 (\y -> y + 1) 0)) term
    line (debug (by_index (\m self -> if m == 0 then 1 else m * self (m - 1)) 10)) term
    line (debug (between (say "a" 1 term) (\x -> x * n) (say "b" 2 term))) term
    Success
