module unsatisfiable_conditions

# Conditions that can never all hold are an error where they are written:
# a function's or lemma's preconditions, a type's conditions on its
# parameters, a constructor's invariants, an alias's predicates, the
# predicates on a class's type.

fn by_bounds x : x~Int, x < 3, x > 5
    x

fn by_false x : x~Int, False
    x

fn by_order x y : x~Int, y~Int, x < y, y < x
    x

fn by_type x : x~Nat, x < 0
    x

type Pos = n~Int, n > 0

fn by_alias x : x~Pos, x < 0
    x

lemma by_lemma x : x~Int, x > 0, x < 0
    ensures x == x

record ByParams lo hi : lo~Int, hi~Int, lo > hi, hi > lo
    value~Int

record ByFields
    value~Int, value < 0, value > 0

enum ByConstructor
    Never x : x~Int, x > 1, x < 1
    Always

type ByAlias = n~Int, n < 0, n > 0

class ByClass a
    fn by_member x -> r : x~a, 1 > 2, r~Bool

class ByClassType s
    type Unit : u~Unit, code s u < 0
    fn code s u -> n : s~ghost Type, u~Unit, n~Nat

# Conditions that can hold are not reported, nor a postcondition.
fn satisfiable x -> r : x~Int, x > 0, x < 10, r~Int, r > x
    x + 1

# A type whose conditions can't hold: its constructors aren't reported too.
record ByBoth lo : lo~Int, lo < 0, lo > 0
    value~Int, value < lo
