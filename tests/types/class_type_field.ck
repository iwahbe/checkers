module class_type_field

# A field of a value whose type is a class's type at a known instance:
# the instance's type is a record, so the field is read.

record Rec
    field~String

record Known
    n~Nat

class Make s
    type Made
    fn make st -> r : st~s, r~Made

instance Make Known
    type Made = Rec
    fn make k
        Rec "x"

fn by_field k -> r : k~Known, r~String
    (make k).field

fn by_let k -> r : k~Known, r~String
    let m = make k
    m.field
