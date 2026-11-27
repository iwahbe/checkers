(set-logic ALL)
; `(as R C)` with no binder named `R`: the constructor `R`, so `f Q` is
; `(mk R)` and the fact is false. (The answer is edited.)
(declare-datatypes ((C 0) (B 0)) (((R) (Q)) ((mk (un C)))))
(declare-fun f (C) B)
(assert (= (f Q) (mk Q)))
(assert (not false))
(check-sat)
