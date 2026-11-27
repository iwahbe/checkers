(set-logic ALL)
; `(R)` applies a constructor to no arguments, which SMT-LIB doesn't
; allow: not read. (The answer is edited.)
(declare-datatypes ((C 0)) (((R) (Q))))
(declare-const c C)
(assert (= c R))
(assert (not false))
(check-sat)
(get-value (c))
