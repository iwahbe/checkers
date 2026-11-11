module refined_messages

# A type mismatch names a refined type as it was written (`Small`), not its
# base type (`Nat`), on both sides, even where the checker compares against
# the base type and proves the refinement separately (D71).

type Small = n~Nat, n < 10

fn result_side o -> r : o~Option Small, r~Small
    o

fn operand_side y -> r : y~Small, r~Small
    y ++ "a"

fn compared y -> r : y~Small, r~Bool
    y == "a"
