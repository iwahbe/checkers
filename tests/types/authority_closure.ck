module authority_closure

# An authority, and a closure that captured one, may be used any number of
# times: called twice, passed to a parameter that isn't `own`, returned.

import std.terminal (Term)

fn say s term -> r : s~String, term~Term, r~Unit
    terminal.print_line s term

fn many f -> r : f~(Unit -> Unit), r~Unit
    f ()
    f ()

fn twice term -> r : term~Term, r~Unit
    let g = \_ -> say "hello" term
    g ()
    g ()

fn passed term -> r : term~Term, r~Unit
    many (\_ -> say "hello" term)

fn returned term -> k : term~Term, k~(Unit -> Unit)
    \_ -> say "hello" term
