(set-logic ALL)
; `E` holds an array of `D` and a sequence of it, and `D` is founded
; first (by `K`): Z3 5.3.3 accepts the group.
(declare-datatypes ((D 0) (E 0)) (((K) (KK (h E))) ((L (g (Seq D)) (a (Array Int D))))))
(declare-const x E)
(assert (= x (L (seq.unit K) ((as const (Array Int D)) K))))
(assert (not false))
(check-sat)
