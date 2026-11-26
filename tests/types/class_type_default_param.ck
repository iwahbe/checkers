module class_type_default_param

# A class's type's default may use the class's parameters: an instance
# that doesn't give the type takes the default at its own types.

class Wrapped a
    type Items = List a
    fn wrap x -> is : x~a, is~Items

# `Items` is `List Int` here.
instance Wrapped Int
    fn wrap x
        [x, x]

record Box b
    item~b

# A head with a type parameter: `Items` is `List (Box b)`.
instance Wrapped (Box b)
    fn wrap x
        [x]

# Given here, the default isn't used.
instance Wrapped Bool
    type Items = Option Bool
    fn wrap x
        Some x

# Several parameters.
class Keyed k v
    type Entry = (k, v)
    fn entry x y -> e : x~k, y~v, e~Entry

instance Keyed String Int
    fn entry x y
        (x, y)

# At a known instance it is the type the default gives there.
fn ints -> is : is~List Int
    wrap 3

fn boxes -> bs : bs~List (Box String)
    wrap (Box "b")

fn first -> o : o~Option Bool
    wrap True

fn pair -> e : e~(String, Int)
    entry "a" 1

# In generic code it is a type of its own.
fn twice x -> r : Wrapped a, x~a, r~(Wrapped.Items a, Wrapped.Items a)
    (wrap x, wrap x)

check ints == [3, 3]
check boxes == [Box "b"]
check first == Some True
check pair == ("a", 1)
check twice 1 == ([1, 1], [1, 1])
