(set-logic ALL)
; `S!val!00` is not how Z3 spells an element (it would be `S!val!0`):
; the model is not read. (The answer is edited.)
(declare-sort S 0)
(declare-const a S)
(declare-const b S)
(assert (not (= a b)))
(assert (not false))
(check-sat)
