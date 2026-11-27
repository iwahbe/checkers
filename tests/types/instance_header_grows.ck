module instance_header_grows

# A type's header clause that asks for a bigger type of its own: finding
# `C (T Int)` needs `C (T (List Int))`, which needs `C (T (List (List Int)))`,
# without end. There is no instance.

class C a
    fn size x -> r : x~a, r~Int

record T a : C (T (List a))
    x~a

instance C (T a)
    fn size x
        0

fn sized t -> r : t~T Int, r~Int
    C.size t
