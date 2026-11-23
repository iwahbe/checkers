module class_alias_explicit

# A refinement alias passed for a class's parameter explicitly: the values
# of it inside the result are checked at the call, with what the
# instance's signature says of the call's arguments.

class Read t
    fn read x t -> r : x~Int, t~ghost Type, r~Option t

instance Read Int
    fn read x t -> r : x~Int, t~ghost Type, r~Option Int,
                       match r
                           Some v -> v == x
                           None   -> True
        Some x

fn by_type -> r : r~Option Nat
    Read.read (-1) Nat

fn by_fact -> n : n~Nat
    match Read.read 5 Nat
        Some v -> v
        None   -> 0
