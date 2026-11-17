module abstract_type_result

# An abstract type of another module, applied, as the result of a type
# function: a type, not a use of its constructor (D172 a).

import std.future (Future)

enum Shape
    One
    Many

fn futures s a -> t : s~Shape, a~Type, t~Type
    match s
        One  -> Future a
        Many -> Array (Future a)

fn wrapped a -> t : a~Type, t~Type
    Future (Array a)
