# Two different types of the same name, in one message, are told apart by
# how this module refers to each: `T` is `same_name.a`'s, imported
# unqualified, and `b.T` is `same_name.b`'s.
module same_name_types

import same_name.a (T)
import same_name.b

fn mismatch t -> r : t~b.T, r~T
    t

# Inside a type: `List T` and `List b.T`.
fn nested ts -> r : ts~List b.T, r~List T
    ts

# The same type twice is shown as written.
fn same t -> r : t~T, r~Int
    t
