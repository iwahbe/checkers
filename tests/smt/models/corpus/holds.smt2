(set-logic ALL)
; Z3's values make every assertion hold.
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
(get-value (x))
