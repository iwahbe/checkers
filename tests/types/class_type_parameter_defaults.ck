module class_type_parameter_defaults

class Wrapped a
    type Value = List a
    fn wrap x -> y : x~a, y~Value

instance Wrapped Int
    fn wrap renamed
        [renamed]

instance Wrapped (List b)
    fn wrap xs
        [xs]

instance Wrapped Bool
    type Value = Int
    fn wrap flag
        1

fn concrete -> xs : xs~List Int
    wrap 1

fn parameterized xs -> ys : xs~List b, ys~List (List b)
    wrap xs

fn overridden -> n : n~Int
    wrap True

class Paired a b
    type Both = (a, b)
    fn pair x y -> z : x~a, y~b, z~Both

instance Paired (List b) a
    fn pair left right
        (left, right)

fn multiple xs x -> result : xs~List b, x~a, result~(List b, a)
    pair xs x
