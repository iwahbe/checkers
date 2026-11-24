module class_home.sealed

export class Size a
    fn size x -> n : x~a, n~Int

# Sealed: importers know only the class's signature.
export record Box
    v~Int

instance Size Box
    fn size b
        1

# Sealed, with a signature of its own: importers know that.
export record Pos
    v~Int

instance Size Pos
    fn size p -> n : p~Pos, n~Int, n == 1
        1

# Transparent: importers see its body.
export record Open
    v~Int

instance Size Open
    transparent fn size o
        1

# Transparent, calling an exported function, which stays sealed.
export fn one u -> n : u~Int, n~Int
    1

export record Calls
    v~Int

instance Size Calls
    transparent fn size c
        one c.v
