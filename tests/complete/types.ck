module types

# Types and conditions in signatures (D142).

record Point
    x~Int
    y~Int

# After `~`: `ghost`, `own`, `comptime`, type parameters, then types.
fn first xs -> r : xs~List a, r~‸

# Inside a type: no keywords.
fn second xs -> r : xs~List ‸

# A condition: the parameters, `forall`, classes.
fn third x -> r : x~Int, r~Int, ‸

# A record's field: `ghost` only.
record Box
    item~‸
