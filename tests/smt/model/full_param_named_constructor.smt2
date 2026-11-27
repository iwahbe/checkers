(set-logic ALL)
; A parameter named as a constructor: in the body the name is the
; parameter, the innermost binder of it. (The answer is edited.)
(declare-datatypes ((C 0) (B 0)) (((R) (Q)) ((mk (un C)))))
(declare-fun f (C) B)
(assert (= (f Q) (mk Q)))
(assert (not false))
(check-sat)
