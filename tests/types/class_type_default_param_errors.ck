module class_type_default_param_errors

import std.list (length)

# A default using the class's parameter is taken at each instance that
# doesn't give the type, with the type's constraints checked there.

class Wrapped a
    type Items = List a
    fn wrap x -> is : x~a, is~Items

# An instance may give another type, so generic code can't use the
# default's.
fn generic x -> is : Wrapped a, x~a, is~List a
    wrap x

# A clause on the type: each instance's must have it.
class Sorted a
    type Keys = List a : Ord Keys
    fn keys x -> ks : x~a, ks~Keys

instance Sorted Int
    fn keys x
        [x]

record Opaque
    n~Int

instance Sorted Opaque
    fn keys x
        [x]

# A predicate on the type, about the instance's functions.
class Short s
    type Run = List s : r~Run, size s r < 3
    fn size s r -> n : s~ghost Type, r~Run, n~Nat

record Wrapping
    n~Nat

instance Short Wrapping
    fn size s r
        length r % 3

record Raw
    n~Nat

instance Short Raw
    fn size s r
        length r
