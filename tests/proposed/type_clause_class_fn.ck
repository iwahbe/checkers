module type_clause_class_fn

# A class's function takes no implied clause: the clause is written in its
# signature.

record Packed s : Seq s
    items~s

class Measure t
    fn measure p -> n : p~Packed t, n~Nat

# Expected:
#
# error[E0284]: no instance of `Seq` for `t`
#   --> type_clause_class_fn.ck:10:27
#    |
# 10 |     fn measure p -> n : p~Packed t, n~Nat
#    |                           ^^^^^^ `t` is a type parameter
#    = help: add `Seq t` to the function's signature
