module instance_refined_generic

# Generic code sees only the class's signature, even where every instance
# promises more.

class Size a
    fn size x -> n : x~a, n~Int

instance Size (List a)
    fn size xs -> n : xs~List a, n~Int, n >= 0
        match xs
            []        -> 0
            _ :: rest -> 1 + size rest

fn generic xs -> r : Size a, xs~a, r~Int, r >= 0
    Size.size xs
