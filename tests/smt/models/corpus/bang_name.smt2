(set-logic ALL)
; A query that introduces a name with `!`, as Z3's own names are: its
; answer is not read, and the run fails.
(declare-const |x!1| Int)
(assert (= |x!1| 1))
(assert (not false))
(check-sat)
(get-value (|x!1|))
