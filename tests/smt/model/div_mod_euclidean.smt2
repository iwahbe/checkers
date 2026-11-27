(set-logic ALL)
; Euclidean: the remainder is never negative, whatever the signs.
(assert (not (and (= (div (- 7) 2) (- 4)) (= (mod (- 7) 2) 1) (= (div 7 (- 2)) (- 3)) (= (mod 7 (- 2)) 1) (= (div (- 7) (- 2)) 4) (= (mod (- 7) (- 2)) 1) (= (div 7 2) 3) (= (mod 7 2) 1))))
(check-sat)
