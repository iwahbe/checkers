(set-logic ALL)
; An array value with a `store` over an uninterpreted index sort whose
; size isn't printed has no normal form: that value is not determined,
; and the other values are read.
(declare-sort S 0)
(declare-const s S)
(declare-const t S)
(declare-const a (Array S Int))
(declare-const x Int)
(assert (not (= s t)))
(assert (= (select a s) 3))
(assert (= (select a t) 4))
(assert (= x 2))
(assert (not false))
(check-sat)
(get-value (a x))
