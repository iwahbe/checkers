module instance_refines_inside_ok

# Refinements inside an instance's signature's types that refine its
# class's: a result's type argument promising more, a parameter's
# requiring less, a function parameter's in both directions.

record Box
    v~Int

class Get a
    fn get w -> r : w~a, r~Option Int

instance Get Box
    fn get w -> r : w~Box, r~Option Nat
        Some 1

class First a
    fn first w xs -> r : w~a, xs~List Nat, r~Int

instance First Box
    fn first w xs -> r : w~Box, xs~List Int, r~Int
        match xs
            x :: _ -> x
            []     -> 0

class Call a
    fn call w f -> r : w~a, f~(Int -> Int), r~Int

instance Call Box
    fn call w f -> r : w~Box, f~(Nat -> Int), r~Int
        f 1

class Gives a
    fn gives w f -> r : w~a, f~(Int -> Nat), r~Int

instance Gives Box
    fn gives w f -> r : w~Box, f~(Int -> Int), r~Int
        f (-1)

class Pairs a
    fn pairs w -> r : w~a, r~(Int, (n~Int, n > 1))

instance Pairs Box
    fn pairs w -> r : w~Box, r~(Int, (n~Int, n > 2))
        (0, 3)

class Same a
    fn same w -> r : w~a, r~Option Nat

instance Same Box
    fn same w -> r : w~Box, r~Option (n~Int, n >= 0)
        Some 0

fn by_get w -> r : Get a, w~a, r~Int
    match Get.get w
        Some n -> n
        None   -> 0

check by_get (Box 0) == 1
check first (Box 0) [7] == 7
check call (Box 0) (\x -> x) == 1
check gives (Box 0) (\x -> 0) == 0
check pairs (Box 0) == (0, 3)
