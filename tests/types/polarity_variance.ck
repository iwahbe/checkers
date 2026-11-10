module polarity_variance

# D16 marks give D71 variance: `+` covariant, `-` contravariant, unmarked invariant.

import std.future (Future)

type Small = n~Nat, n < 10

export abstract record Box +v : v~Type
    item~v

export abstract record Sink -v : v~Type
    put~(v -> Nat)

export abstract record Cell v : v~Type
    item~v

fn box_forget b -> c : b~Box Small, c~Box Nat
    b

fn sink_gain s -> t : s~Sink Nat, t~Sink Small
    s                                           # fine: takes any `Nat`, so any `Small`

fn future_forget f -> g : f~Future Small, g~Future Nat
    f

fn sink_bad s -> t : s~Sink Small, t~Sink Nat
    s                                           # error E0262: needs a `Small`

fn cell_bad c -> d : c~Cell Small, d~Cell Nat
    c                                           # error E0262: unmarked, so invariant
