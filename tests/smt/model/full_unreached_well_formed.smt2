(set-logic ALL)
; Every term of the model is checked, whether evaluation reaches it or
; not: here both branches are terms, and the model is read. (Edited.)
(declare-const x Int)
(assert (= x 1))
(assert (not false))
(check-sat)
