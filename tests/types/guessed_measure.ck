# #641: with no `decreasing`, a function whose recursion isn't structural
# gets a measure guessed from its parameters' sizes and its guards'
# distances, which the prover checks.
module guessed_measure

fn fib x -> n : x~Nat
    if x == 0 or x == 1 then 1 else fib (x - 1) + fib (x - 2)

check fib 6 == 13

# Any integer the facts show is `>= 0`, refined or not.
fn halves x -> n : x~Nat, x % 2 == 0
    if x == 0 then 0 else halves (x - 2) + 1

# A guard's distance: up to a bound.
fn count_from i n -> r : i~Nat, n~Nat
    if i < n then count_from (i + 1) n + 1 else 0

# A guard's distance: negative numbers rising to zero.
fn up x -> n : x~Int
    if x < 0 then up (x + 1) + 1 else 0

check halves 6 == 3
check count_from 2 5 == 3
check up (-3) == 3

# Up to a bound that is an expression (`decreasing len src - i`).
fn skip_spaces src i -> j : src~Bytes, i~Nat, i <= len src, j~Nat
    if i < len src and src[i] == ' ' then skip_spaces src (i + 1) else i

# Functions that call each other.
fn even n : n~Nat
    if n == 0 then True else odd (n - 1)

fn odd n : n~Nat
    if n == 0 then False else even (n - 1)

# Nothing gets smaller: no measure is found.
fn grow x -> n : x~Int
    if x > 100 then 0 else grow (x - 1) + 1

check skip_spaces b"  x" 0 == 2
check even 4
