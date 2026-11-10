module partial_pre

import std.string
import std.list

# A function with a precondition can be partially applied (D86): `mid 0`
# has the type `(b~Nat -> m~Nat, 0 <= b)`, checked where it is passed (D85).
fn mid a b -> m : a~Nat, b~Nat, a <= b, m~Nat
    a + (b - a) / 2

fn fine_nat xs -> ys : xs~List Nat, ys~List Nat
    list.map (mid 0) xs

# ...but not where the function may be given an argument it doesn't accept.
fn bad xs -> ys : xs~List Nat, ys~List Nat
    list.map (mid 3) xs

# A refinement alias parameter is met where the expected function type
# promises the alias.
fn shout c -> s : c~Char, s~String
    string.from_char c

fn fine s -> t : s~String, t~String
    string.concat_map shout s
