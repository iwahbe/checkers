module single_use

# A closure that captured an authority holds one use of it, so it may be
# called at most once: where it is made, bound with `let` and called once
# (or never), or passed to a parameter declared `own`. Called twice, passed
# to a parameter that isn't `own`, or returned, it is E0409.

import std.terminal (Term)

fn run f -> r : f~own (Unit -> Unit), r~Unit
    f ()

fn many f -> r : f~(Unit -> Unit), r~Unit
    f ()

fn say s term -> r : s~String, term~Term, r~Unit
    terminal.print_line s term

fn twice term -> r : term~Term, r~Unit
    let g = \_ -> say "hello" term
    g ()
    g ()

fn once term -> r : term~Term, r~Unit
    let g = \_ -> say "hello" term
    g ()

fn never term -> r : term~Term, r~Unit
    let g = \_ -> say "hello" term
    ()

fn branches b term -> r : b~Bool, term~Term, r~Unit
    let g = \_ -> say "hello" term
    if b
        g ()
    else
        g ()

fn keep x -> r : x~a, r~Unit
    ()

# Its result is a value of its own: passing it on doesn't pass the closure.
fn in_argument term -> r : term~Term, r~Unit
    let g = \_ -> say "hello" term
    keep (g ())

fn made term -> r : term~Term, r~Unit
    (\_ -> say "hello" term) ()

fn to_own term -> r : term~Term, r~Unit
    run (\_ -> say "hello" term)

fn to_many term -> r : term~Term, r~Unit
    many (\_ -> say "hello" term)

fn by_let term -> r : term~Term, r~Unit
    let g = \_ -> say "hello" term
    many g

fn returned term -> k : term~Term, k~(Unit -> Unit)
    \_ -> say "hello" term

# Passing the authority as a parameter: called any number of times.
fn param term -> r : term~Term, r~Unit
    let g = \t -> say "hello" t
    g term
    g term

fn partly term -> r : term~Term, r~Unit
    let g = say "hello"
    g term
    g term

fn partial_captured term -> r : term~Term, r~Unit
    let g = flip_say term
    g "a"
    g "b"

fn flip_say term s -> r : term~Term, s~String, r~Unit
    say s term

# A closure that captured such a closure captured the authority too.
fn through term -> r : term~Term, r~Unit
    let g = \_ -> say "hello" term
    let h = \_ -> g ()
    h ()
    h ()

fn through_many term -> r : term~Term, r~Unit
    let g = \_ -> say "hello" term
    many (\_ -> g ())

record Caps
    term~Term

# An authority inside a value the closure captured.
fn inside term -> r : term~Term, r~Unit
    let caps = Caps term
    let g = \_ -> say "hello" caps.term
    g ()
    g ()

# A generic function may call a parameter that isn't `own` any number of
# times, and its proof takes the calls to be equal.
fn need x y -> r : x~a, y~a, x == y, r~Unit
    ()

fn both f -> r : f~(Unit -> a), r~Unit
    need (f ()) (f ())

fn generic term -> r : term~Term, r~Unit
    both (\_ -> terminal.read_line term)
