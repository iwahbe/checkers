module instance_recursion_type_param

# Inside an instance, a member that takes the class's parameter explicitly
# passes it on in a recursive call, as the class's signature takes it, and
# so does a call of another member, and a lemma's proof. What it passes is the instance's type.

class Count a
    fn count xs a -> r : xs~List Int, a~ghost Type, r~Nat
    fn evens xs a -> r : xs~List Int, a~ghost Type, r~Nat

record Ones
    seen~Nat

instance Count Ones
    fn count xs a
        match xs
            []        -> 0
            x :: rest -> (if x == 1 then 1 else 0) + count rest a

    fn evens xs t
        count xs t

check Count.count [1, 2, 1] Ones == 2

record Twos
    seen~Nat

instance Count Twos
    fn count xs a
        match xs
            []        -> 0
            _ :: rest -> evens rest a

    fn evens xs a
        match xs
            []        -> 0
            _ :: rest -> 1 + count rest a

check Count.count [1, 2, 1] Twos == 1

class Bound a
    fn size xs a -> r : xs~List Int, a~ghost Type, r~Int
    lemma small xs a : xs~List Int, a~ghost Type
        ensures size xs a <= len xs

instance Bound Ones
    fn size xs a
        match xs
            []        -> 0
            x :: rest -> (if x == 1 then 1 else 0) + size rest a

    lemma small xs a
        proof
            match xs
                []        -> ()
                _ :: rest -> small rest a

fn wrong xs -> r : xs~List Int, r~Nat
    0

instance Count Int
    fn count xs a
        match xs
            []        -> 0
            _ :: rest -> count rest Ones

    fn evens xs _
        wrong xs
