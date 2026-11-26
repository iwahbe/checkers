module field_of_call

# A field whose type depends on an earlier field, read from a call's result:
# the call runs when the field's type needs its value, and not before.

fn pick b -> t : b~Bool, t~Type
    if b then Nat else String

record Tagged
    counts~Bool
    value~pick counts

fn make n -> r : n~Nat, r~Tagged
    Tagged True n

export fn by_field n -> v : n~Nat, v~Nat
    (make n).value

export fn wrong n -> v : n~Nat, v~String
    (make n).value
