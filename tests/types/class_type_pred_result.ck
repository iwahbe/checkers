module class_type_pred_result

# A class's type's predicates hold of a class function's result in generic
# code: used directly, bound by `let`, or inside a part of it.

class Encoding s
    type Unit : u~Unit, code s u < 256
    fn code s u -> n : s~ghost Type, u~Unit, n~Nat
    fn one x -> u : x~s, u~Unit
    fn two x -> p : x~s, p~(Unit, Unit)

fn direct x -> b : Encoding s, x~s, b~U8
    code s (one x)

fn by_let x -> b : Encoding s, x~s, b~U8
    let u = one x
    code s u

fn by_part x -> b : Encoding s, x~s, b~U8
    let (_, u) = two x
    code s u
