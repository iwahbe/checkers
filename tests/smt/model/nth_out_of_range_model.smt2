(set-logic ALL)
; Out of range, seq.nth is unspecified: a function of the sequence and the index.
(assert (= (seq.nth (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)) 3) 9))
(assert (= (seq.nth (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)) (- 1)) 8))
(assert (not false))
(check-sat)
(get-value ((seq.nth (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)) 3) (seq.nth (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)) (- 1))))
