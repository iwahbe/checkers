(set-logic ALL)
; A model defines only what the query declares and Z3's own names: a
; definition of a constructor is not read. (The answer is edited.)
(declare-datatypes ((C 0)) (((R) (Q))))
(declare-const c C)
(assert (= c Q))
(assert (not false))
(check-sat)
