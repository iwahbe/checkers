(set-logic ALL)
; A lambda captures a let-bound variable; select applies it.
(assert (not (= (let ((k 5)) (select (lambda ((i Int)) (+ i k)) 2)) 7)))
(check-sat)
