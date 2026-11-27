(set-logic ALL)
; A let binds all its names at once, in the outer scope; an inner let shadows.
(assert (not (and (= (let ((x 1)) (let ((x 2) (y x)) (+ (* 10 x) y))) 21) (= (let ((x 1)) (let ((x (+ x 1))) (let ((x (* x 3))) x))) 6))))
(check-sat)
