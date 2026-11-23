# A module with no obligations still asks Z3 whether its branches run
# (W022): `checkers trust` counts those queries, the second function's
# reused from the first's.
module probes_counted

fn first n -> m : n~Nat, m~Nat
    if n > 3 then 1 else 2

fn second n -> m : n~Nat, m~Nat
    if n > 3 then 1 else 2
