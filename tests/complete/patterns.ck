module patterns

# Patterns and imports (D142).
import std.‸

enum Shape
    Circle r : r~Nat
    Square s : s~Nat

# A `match` arm: the constructors of the type matched.
fn area s -> n : s~Shape, n~Nat
    match s
        Circle r -> r * r * 3
        ‸
