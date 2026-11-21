module class_type_default_kind

class C f
    type T = f Int
    fn count x -> n : x~T, n~Int

instance C List
    fn count xs
        1

fn projection -> xs : xs~C.T List
    [1]
