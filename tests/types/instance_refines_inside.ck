module instance_refines_inside

# An instance's signature is compared with its class's refinements inside
# its types too: a type argument, and a function type's parameter.

record Box
    v~Int

class Get a
    fn get w -> r : w~a, r~Option Nat

instance Get Box
    fn get w -> r : w~Box, r~Option Int
        Some (-1)

class First a
    fn first w xs -> r : w~a, xs~List Int, r~Nat

instance First Box
    fn first w xs -> r : w~Box, xs~List Nat, r~Nat
        match xs
            x :: _ -> x
            []     -> 0

class Call a
    fn call w f -> r : w~a, f~(Nat -> Nat), r~Nat

instance Call Box
    fn call w f -> r : w~Box, f~(Int -> Nat), r~Nat
        f (-1)

class Gives a
    fn gives w f -> r : w~a, f~(Nat -> Int), r~Int

instance Gives Box
    fn gives w f -> r : w~Box, f~(Nat -> Nat), r~Int
        f 1

class Pairs a
    fn pairs w -> r : w~a, r~(Int, (n~Int, n > 2))

instance Pairs Box
    fn pairs w -> r : w~Box, r~(Int, (n~Int, n > 1))
        (0, 2)
