module partial_pre

import string
import list

# A function with a precondition can't be partially applied (D51)...
fn mid a b -> m : a~Nat, b~Nat, a <= b, m~Nat
    a + (b - a) / 2

fn bad xs -> ys : xs~List Nat, ys~List Nat
    list.map (mid 0) xs

# ...except where the expected function type promises a refinement alias.
fn shout c -> s : c~Char, s~String
    string.from_char c

fn fine s -> t : s~String, t~String
    string.concat_map shout s
