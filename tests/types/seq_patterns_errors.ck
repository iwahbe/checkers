module seq_patterns_errors

# Sequence patterns can't be mixed with the type's own constructors; they
# cover what `[]` and `_ :: _` cover; a type without a `Seq` instance has
# none.

fn mixed s -> n : s~String, n~Nat
    match s
        String b -> 0
        _ :: _   -> 1

fn missing xs -> n : Seq s, xs~s, n~Nat
    match xs
        [x] -> 1

fn nested xs -> n : xs~Bytes, n~Nat
    match xs
        []          -> 0
        _ :: _ :: _ -> 2

record Box
    x~Int

fn no_instance b -> n : b~Box, n~Nat
    match b
        []     -> 0
        _ :: _ -> 1
