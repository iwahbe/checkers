# Arrays are ordered when their elements are: by the first elements where
# they differ, an array before any longer one that starts with it. `Bytes`
# is one case.
module array_order

fn lt a b -> r : a~Bytes, b~Bytes, r~Bool
    a < b

# The instance's lemmas, at arrays of any ordered type.
fn ordered xs ys -> r : Ord a, xs~Array a, ys~Array a, r~Bool, r
    have total xs ys
    xs <= ys or ys <= xs

fn equal xs ys -> r : Ord a, xs~Array a, ys~Array a, xs <= ys, ys <= xs, r~Bool, r
    have antisym xs ys
    xs == ys

# What the order is, at known arrays.
check b"" <= b"a"
check b"ab" <= b"ab"
check b"ab" < b"abc"
check b"ab" < b"b"
check not (b"b" <= b"ab")
check b"\x7F" < b"\x80"

# Not every array comes before a longer one.
fn wrong xs ys -> r : xs~Bytes, ys~Bytes, len xs < len ys, r~Bool, r
    xs <= ys
