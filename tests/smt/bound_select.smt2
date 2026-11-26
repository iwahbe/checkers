; A bound variable of array sort is read with `select`, and a `define-fun`
; may be applied in a `forall`'s body, outside its patterns.
(set-logic ALL)
(declare-fun g (Int) Int)
(define-fun h ((m (Array Int Int))) Int (select m 1))
(define-fun pos ((y Int)) Bool (> y 0))
(assert (forall ((i Int)) (! (pos (g i)) :pattern ((g i)))))
(assert (not (= (h ((as const (Array Int Int)) 5)) 5)))
(check-sat)
