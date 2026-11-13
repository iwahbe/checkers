module forall_hyps

# Named `forall` preconditions (D137): proved where the function is called,
# with fresh values; used in the body only by name, with `have`.

fn ordered le x y -> r : le~(Int -> Int -> Bool), x~Int, y~Int,
                         total: forall a b : a~Int, b~Int, le a b or le b a, r~Bool, r
    have total x y
    le x y or le y x

# A function passing its own hypothesis on.
fn twice le x -> r : le~(Int -> Int -> Bool), x~Int, total: forall a b : a~Int, b~Int, le a b or le b a, r~Bool, r
    ordered le x x

# A comparison that is total: nothing more to write.
fn uses -> r : r~Bool, r
    ordered (\a b -> a <= b) 1 2

# Not total: `a < b` fails for equal values.
fn strict -> r : r~Bool
    ordered (\a b -> a < b) 1 1

# After `implies`: the `forall` is filled in, the rest is a fact.
fn below n k -> r : n~Nat, k~Nat, k < n, h : n > 0 implies forall i : i~Nat, i < n, i + 1 <= n, r~Bool, r
    have h k
    k + 1 <= n

check uses and below 3 1

# Wrong uses.
fn unnamed x -> r : x~Int, forall a : a~Int, a == a, r~Bool
    True

fn before x -> r : x~Int, h: (forall a : a~Int, a > x) implies x > 0, r~Bool
    True

fn too_many x -> r : x~Int, h: forall a : a~Int, a + 1 > a, r~Bool, r
    have h x x
    True

fn too_few x -> r : x~Int, h: forall a b : a~Int, b~Int, a + b == b + a, r~Bool, r
    have h x
    True

fn elsewhere x -> r : x~Int, r~Bool, r
    forall a : a~Int, a == a
