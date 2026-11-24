# A field's or constructor's condition may rely on the conditions before it,
# as a function's may (#108).
module field_condition_order

fn pred a b : a~Nat, b~Nat, a <= b
    True

record Same start : start~Nat
    stop~Nat, start <= stop, pred start stop

# A later field relies on an earlier field's conditions.
record Later start : start~Nat
    stop~Nat, start <= stop
    value~Nat, pred start stop

enum Pair
    Pair start stop : start~Nat, stop~Nat, start <= stop, pred start stop

# Only those before it: here the call comes first.
record Before start : start~Nat
    stop~Nat, pred start stop, start <= stop
