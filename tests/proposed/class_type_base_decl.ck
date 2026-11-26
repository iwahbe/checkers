module class_type_base_decl

# A base type is one type: not two, and not one naming the class's
# parameter (proposed, #360). Naming the type itself as well says the same.
# Expected: E0370 at `u~Nat`, "`Unit` has one base type"; E0370 at
# `u~List s`, "the base type of `Unit` can't mention the class's parameter
# `s`"; `Both` and `small` check.

class Both s
    type Unit : u~Unit, u~Int, u < 256
    fn both x -> u : x~s, u~Unit

class Two s
    type Unit : u~Int, u~Nat
    fn two x -> u : x~s, u~Unit

class Mine s
    type Unit : u~List s
    fn mine x -> u : x~s, u~Unit

fn small x -> r : Both s, x~s, r~Bool, r
    both x < 256
