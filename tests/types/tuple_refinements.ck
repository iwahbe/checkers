module tuple_refinements

# A tuple's parts keep their refinements when a pattern takes it apart (D71,
# D82): each part at a refined type is known to satisfy it.

fn plain t -> r : t~(Bool, (s~Nat, s > 3)), r~Nat, r > 3
    match t
        (_, s) -> s

# The refinement may mention the function's parameters.
fn after k t -> r : k~Nat, t~(Bool, (s~Nat, k < s)), r~Nat, r > k
    match t
        (_, s) -> s

# Inside an `Option`, as `utf8.decode_at` gives it.
fn step k o -> r : k~Nat, o~Option (Bool, (s~Nat, k < s)), r~Nat, r > k
    match o
        Some (_, s) -> s
        None        -> k + 1

# Three parts are two, the last a pair (D174): each keeps its refinement.
fn last t -> r : t~(Bool, Bool, (s~Nat, s > 3)), r~Nat, r > 3
    match t
        (_, _, s) -> s

fn middle t -> r : t~(Bool, (s~Nat, s > 3), Bool), r~Nat, r > 3
    match t
        (_, s, _) -> s

# A tuple written inside a part.
fn inner t -> r : t~(Bool, ((s~Nat, s > 3), Bool), Bool), r~Nat, r > 3
    match t
        (_, (s, _), _) -> s

# A `Nat` part is non-negative.
fn nat t -> r : t~(Bool, Nat), r~Nat
    match t
        (_, n) -> n

# Only what the refinement says: `s > 3` doesn't give `s > 4`.
fn wrong t -> r : t~(Bool, (s~Nat, s > 3)), r~Nat, r > 4
    match t
        (_, s) -> s
