module check_runtime_error

# A `check` that stops with a runtime error is E0261 (D40); evaluating it
# as native code (D80) must report it, not end `checkers`. The checks after
# it still run.

fn steps n -> r : n~Nat, r~Nat
    n - 3

check steps 2 == 0
check steps 5 == 2
check steps 7 == 5
