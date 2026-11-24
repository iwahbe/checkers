# A condition on a type's parameters is checked wherever the type is
# written, holds in the type's fields, and its calls are checked (#136).
module type_param_conditions

fn pred a b : a~Nat, b~Nat, a <= b
    True

record Ordered lo hi : lo~Nat, hi~Nat, lo <= hi
    value~Nat

# The condition holds in the fields.
record InFields lo hi : lo~Nat, hi~Nat, lo <= hi
    value~Nat, pred lo hi

# A condition may rely on those before it.
enum Later lo hi : lo~Nat, hi~Nat, lo <= hi, pred lo hi
    Later

# Only those before it: here the call comes first.
enum Before lo hi : lo~Nat, hi~Nat, pred lo hi, lo <= hi
    Before

fn literal -> r : r~Ordered 5 1
    Ordered 0

fn by_precondition lo hi -> r : lo~Nat, hi~Nat, lo <= hi, r~Ordered lo hi
    Ordered 0

# A precondition written after the type counts too.
fn precondition_after lo hi -> r : lo~Nat, hi~Nat, r~Ordered lo hi, lo <= hi
    Ordered 0

fn no_precondition lo hi -> r : lo~Nat, hi~Nat, r~Ordered lo hi
    Ordered 0

# A postcondition is not a fact here.
fn by_postcondition lo hi -> r : lo~Nat, hi~Nat, r~Ordered lo hi, r.value == 0 and lo <= hi
    Ordered 0

fn in_parameter x : x~Ordered 3 2
    True

record FieldType
    inner~Ordered 2 1

# A field may write the type under its own type's condition.
record Holder lo hi : lo~Nat, hi~Nat, lo <= hi
    inner~Ordered lo hi

enum Wrapper lo hi : lo~Nat, hi~Nat, lo <= hi
    Wrapper inner : inner~Ordered lo hi
