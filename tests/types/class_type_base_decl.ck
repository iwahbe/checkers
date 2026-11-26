module class_type_base_decl

# Typings of a class's type's value combine, as a parameter's do: `u~Int,
# u~Nat` is an `Int` that is also a `Nat`, and naming the type itself as
# well says the same. Typings that don't agree are an error.

class Both s
    type Unit : u~Unit, u~Int, u < 256
    fn both x -> u : x~s, u~Unit

fn small x -> r : Both s, x~s, r~Bool, r
    both x < 256

class Two s
    type Unit : u~Int, u~Nat
    fn two x -> u : x~s, u~Unit

fn natural x -> n : Two s, x~s, n~Nat
    two x

instance Two Bool
    type Unit = Int
    fn two x
        0

class Clash s
    type Unit : u~Int, u~Bool
    fn clash x -> u : x~s, u~Unit
