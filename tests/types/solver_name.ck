# A function whose qualified name is one of the solver's own (`seq.unit`,
# at the same argument sorts) is still the program's function to it: the
# lemma about it proves.
module seq

fn unit x -> r : x~Nat, r~Nat
    match x
        0 -> 0
        _ -> unit (x - 1)

lemma unit_zero x : x~Nat
    ensures unit x == 0
    proof
        match x
            0 -> auto
            _ -> have unit_zero (x - 1)
