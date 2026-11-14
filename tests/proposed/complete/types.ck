module types

record Point
    x~Int
    y~Int

# In a signature, after `~`.
fn first xs -> r : xs~List a, r~‸

# Keywords: `ghost`, `own`, `comptime`.
# Names: type parameters in scope (`a`), then types: Point, then the
# prelude's (Int, Nat, Bool, String, List, Option, …) and type aliases.
# Not: functions, constructors, locals other than type parameters.
# Typing `r~Op` narrows to `Option`.
