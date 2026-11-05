module mismatch

record Point
    x~Int
    y~Int

fn wrong_arg -> n : n~Nat
    1 + "two"

fn wrong_result -> s : s~String
    42

fn branches b -> r : b~Bool, r~Nat
    if b then 1 else "no"

fn too_many -> n : n~Nat
    let f = \x -> x + 1
    f 1 2

fn unknown -> n : n~Nat
    undefined_thing 1

fn no_field p -> n : p~Point, n~Int
    p.z

fn not_a_record n -> m : n~Nat, m~Nat
    n.value

fn strings_dont_add -> s : s~String
    "a" + "b"

fn len_of_number -> n : n~Nat
    len 5

fn discarded -> n : n~Nat
    1 + 1
    2

fn needs_type x
    x

fn ok -> n : n~Nat
    1
