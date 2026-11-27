(set-logic ALL)
; `(as R C)` where `R` is a parameter: `as` names a constructor or
; `seq.empty`, never a bound name, so the model is not read. (Edited.)
(declare-datatypes ((C 0) (B 0)) (((R) (Q)) ((mk (un C)))))
(declare-fun f (C) B)
(assert (= (f Q) (mk Q)))
(assert (not false))
(check-sat)
