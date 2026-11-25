module typed_twice_disagree

# Typings of one name that can't combine are errors, never ignored.

fn other_base x : x~Int, x~Bool
    x

fn unknown x : x~Int, x~Missing
    x

fn inside xs : xs~List Int, xs~List Nat
    xs

record Pair a : a~Type, a~Int
    left~a
