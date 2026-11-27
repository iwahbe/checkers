(set-logic ALL)
; A universe's cardinality constraint is read, not skipped: one that isn't
; `(or (= x E) …)` is not read, nor is the model. (The answer is edited.)
(declare-sort S 0)
(declare-const a S)
(declare-const b S)
(assert (not (= a b)))
(assert (not false))
(check-sat)
