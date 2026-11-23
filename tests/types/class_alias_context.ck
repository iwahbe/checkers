module class_alias_context

# A refinement alias inside a class's type argument, where the instance's
# context is about it: `Make (List a) : Make a` at `List Nat` uses `Make`
# at `Nat`, `Int`'s instance, for its elements. Where no context is about
# it, the instance is generic in it, which needs nothing (`by_part`).

class Make t
    fn make u -> r : u~Int, r~t

instance Make Int
    fn make u
        u

instance Make (List a) : Make a
    fn make u
        [Make.make u]

class Same t
    fn same xs -> r : xs~t, r~t

instance Same (List a)
    fn same xs
        xs

fn by_context -> ns : ns~List Nat
    make 1

fn by_part xs -> ys : xs~List Nat, ys~List Nat
    same xs
