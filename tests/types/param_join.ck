module param_join

# Values that decide a type parameter together give it the join of their
# types (for numbers, the hull of their ranges), so their order doesn't
# matter: as an argument, a list's element, or under a type constructor.

fn pick x y -> r : x~a, y~a, r~a
    y

fn push x xs -> r : x~a, xs~List a, r~List a
    x :: xs

fn by_call c n -> r : c~Nat, n~Nat, r~(Nat, Nat)
    let m = 4 - c % 4
    let s = pick m n
    let t = pick n m
    (s, t)

fn by_list c n -> r : c~Nat, n~Nat, r~(List Nat, List Nat)
    let m = 4 - c % 4
    let s = [m, n]
    let t = [n, m]
    (s, t)

fn by_type c n ns -> r : c~Nat, n~Nat, ns~List Nat, r~List (List Nat)
    let m = 4 - c % 4
    let s = push m ns
    let t = push n [m]
    [[m], ns, s, t]

# The hull is kept: both ranges' bounds hold of the result.
fn hull c d -> r : c~Nat, d~Nat, r~(r~Nat, 1 <= r, r <= 8)
    let m = 4 - c % 4
    let k = 8 - d % 4
    let s = pick m k
    let t = pick k m
    if c < d then s else t

# A literal is its own range.
fn literal c -> r : c~Nat, r~(r~Nat, 1 <= r, r <= 100)
    let m = 4 - c % 4
    let s = pick m 100
    let t = pick 2 m
    if c < 2 then s else t

# Not a `(r~Nat, r <= 4)`: `n` may be more.
fn wider c n -> r : c~Nat, n~Nat, r~(r~Nat, r <= 4)
    let m = 4 - c % 4
    let s = pick m n
    s

fn mismatch c -> r : c~Nat, r~String
    let m = 4 - c % 4
    pick m "four"
