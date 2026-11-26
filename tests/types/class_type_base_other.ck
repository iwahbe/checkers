module class_type_base_other

# A base type may name the class's other types: at each instance they are
# the instance's.

class Units s
    type Unit : u~Int, u < 256
    type Run : r~List Unit
    fn run x -> r : x~s, r~Run

instance Units Bool
    type Unit = U8
    type Run = List U8
    fn run x
        []

instance Units Int
    type Unit = U8
    type Run = List Int
    fn run x
        []

fn first x -> n : Units s, x~s, n~Int
    match run x
        []     -> 0
        u :: _ -> u
