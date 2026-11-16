# A keyword where a name belongs (E0122): said plainly, with a name to use
# instead. A keyword parameter's constraint isn't reported again.
module keyword_name

fn first own n -> r : own~Nat, n~Nat, r~Nat
    n

fn module -> r : r~Nat
    1

fn fine own_ -> r : own_~Nat, r~Nat
    own_
