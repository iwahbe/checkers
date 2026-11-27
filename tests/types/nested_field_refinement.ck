module nested_field_refinement

# A record's field refinements hold where the record is itself a field
# (#505): `o.inner.v` is a `Small`, as `i.v` is.

type Small = n~Nat, n < 10

record Inner
    v~Small

record Outer
    inner~Inner

record Outermost
    outer~Outer

fn need x -> r : x~Small, r~Nat
    x

fn one i -> r : i~Inner, r~Nat
    need i.v

fn matched o -> r : o~Outer, r~Nat
    match o
        Outer i ->
            match i
                Inner v -> need v

fn direct o -> r : o~Outer, r~Nat
    need o.inner.v

fn stepped o -> r : o~Outer, r~Nat
    let i = o.inner
    need i.v

fn deeper o -> r : o~Outermost, r~Nat
    need o.outer.inner.v
