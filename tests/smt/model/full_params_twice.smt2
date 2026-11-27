(set-logic ALL)
; A definition whose parameters share a name is not SMT-LIB: the model is
; not read. (The answer is edited.)
(declare-fun g (Int Int) Int)
(assert (= (g 1 2) 1))
(assert (not false))
(check-sat)
