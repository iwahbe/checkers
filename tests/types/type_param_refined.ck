# A refinement in a type parameter's typing is a condition on the type,
# as the predicate it stands for is: checked wherever the type is written,
# a fact in its fields.
module type_param_refined

record ByAlias n : n~Nat
    v~Int

enum ByInline n : n~(m~Int, m > 0)
    ByInline

# Several typings of a parameter combine.
record Combined n : n~Int, n~Nat
    v~Int

fn alias_negative -> r : r~ByAlias (-1)
    ByAlias 0

fn alias_zero -> r : r~ByAlias 0
    ByAlias 0

fn inline_zero -> r : r~ByInline 0
    ByInline

fn combined_negative -> r : r~Combined (-1)
    Combined 0

fn by_precondition k -> r : k~Int, k >= 0, r~ByAlias k
    ByAlias 0

fn no_precondition k -> r : k~Int, r~ByAlias k
    ByAlias 0

# The refinement holds in the fields.
fn need_nat n -> r : n~Nat, r~Bool
    True

record InFields n : n~Int, n~Nat
    ok~Bool, ok == need_nat n
