module class_type_default_capture

class C a
    type T = (u~Type -> u -> a)
    fn run x -> y : x~T, y~a

instance C (List u)
    fn run f
        f String "s"

instance C (Option v)
    fn run f
        f String "s"

class D a
    type T = (n~Int -> a)
    fn apply x -> y : x~T, y~a

instance D (List n)
    fn apply f
        f 1
