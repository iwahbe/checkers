module instance_refined_value

# A class's function at a known instance, passed as a value or partially
# applied, has the instance's signature: its stronger postcondition, and
# its weaker precondition. Through a class clause, only the class's.

class Count a
    fn count k x -> n : k~Int, k > 0, x~a, n~Int

instance Count (List a)
    fn count k xs -> n : k~Int, xs~List a, n~Int, n >= k
        k

fn apply f x -> r : f~(y~a -> n~Int, n >= 0), x~a, r~Int
    f x

fn by_value xs -> r : xs~List Int, r~Int
    apply (count 0) xs

fn by_let xs -> r : xs~List Int, r~Int, r >= 0
    let f = count 0
    f xs

fn generic x -> r : Count a, x~a, r~Int
    let f = count 0
    f x

fn generic_value x -> r : Count a, x~a, r~Int
    apply (count 1) x
