(set-logic ALL)
; (mod n 0) is unspecified too, and unrelated to (div n 0).
(assert (= (mod 5 0) (- 9)))
(assert (= (div 5 0) 1))
(assert (not false))
(check-sat)
(get-value ((mod 5 0) (div 5 0)))
