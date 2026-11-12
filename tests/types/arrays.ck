# Arrays (D133): indexing gives the element type, with its refinement;
# `==` compares element by element; `Bytes` is `Array U8`.
module arrays

# An `Int` element needn't be a `U8`: E0450.
fn first_byte xs -> b : xs~Array Int, len xs > 0, b~U8
    xs[0]

# A `U8` element is one, as bytes always were.
fn byte xs -> b : xs~Bytes, len xs > 0, b~U8
    xs[0]

# An array of functions can't be compared: E0263.
fn same fs gs -> r : fs~Array (Int -> Int), gs~Array (Int -> Int), r~Bool
    fs == gs

fn eq xs ys -> r : xs~Array Nat, ys~Array Nat, r~Bool
    xs == ys

# `Bytes` and `Array U8` are one type; an `Array U8` is an `Array Nat`.
fn bytes_of xs -> b : xs~Array U8, b~Bytes
    xs

fn naturals xs -> ns : xs~Bytes, ns~Array Nat
    xs

# Out of bounds: E0450.
fn past xs -> x : xs~Array Nat, x~Nat
    xs[len xs]
