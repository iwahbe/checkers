(set-logic ALL)
; `T ≅ Seq (T → Int)`: `T` reaches an array's index through `G`'s
; parameter, under a sequence. No set is that; rejected (Z3 5.3.3 accepts it).
(declare-datatypes ((Fn 1)) ((par (A) ((fn (ap (Array A Int)))))))
(declare-datatypes ((G 1)) ((par (A) ((g (un (Seq (Fn A))))))))
(declare-datatypes ((T 0)) (((mk (x (G T))))))
(assert (not false))
(check-sat)
