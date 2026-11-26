module type_eq_in_type

# A type equation is a constructor's constraint, not a condition on a type
# (proposed, #209). Expected: E0296 at `t == Int`, "a type equation is a
# function's, a lemma's or a constructor's constraint, not a type's".

enum Tagged t : t~Type, t == Int
    Tag n : n~Int
