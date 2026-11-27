(set-logic ALL)
; A cardinality constraint naming other elements than the universe's
; `declare-fun`s: the model is not read. (The answer is edited.)
(declare-sort S 0)
(declare-const a S)
(declare-const b S)
(assert (not (= a b)))
(assert (not false))
(check-sat)
