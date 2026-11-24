module show_bool_ops

# Facts are shown with `and`, `or` and `implies`, in parentheses where an
# operand binds less tightly than its operator.

lemma grouped x : x~Int, (x > 0 or x < -5) and x != 3, (x > 1 implies x > 2) implies x > 4
    ensures x > 9
