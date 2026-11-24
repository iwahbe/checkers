module class_member_clause

# A class's function with a class clause of its own: an instance needs no
# context for it, and its body and postconditions may use it, at a known
# instance and through a clause.

class Parse a s
    fn parse xs a -> r : Seq s, xs~s, a~ghost Type, r~Option a

instance Parse Bool s
    fn parse xs a
        None

instance Parse Int s
    fn parse xs a
        Some (Seq.size xs)

fn at_list xs -> r : xs~List Int, r~Option Int
    parse xs Int

class Weigh w
    fn weigh by xs -> n : Seq s, by~w, xs~s, n~Int, n <= Seq.size xs

instance Weigh Bool
    fn weigh by xs
        if by then Seq.size xs else 0

fn known xs -> n : xs~List Int, n~Int, n <= 1 + Seq.size xs
    weigh True xs

fn by_clause b xs -> n : Weigh w, Seq s, b~w, xs~s, n~Int, n <= 1 + Seq.size xs
    weigh b xs
