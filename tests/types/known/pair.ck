module known.pair

# Sealed: a module importing this one sees its signature, not its body.
export fn second a b -> r : a~Int, b~Int, b > 0, r~Int
    b
