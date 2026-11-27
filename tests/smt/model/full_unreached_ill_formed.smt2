(set-logic ALL)
; Every term of the model is checked, whether evaluation reaches it or
; not: an `ite` whose other branch isn't a term is not read. (Edited.)
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
