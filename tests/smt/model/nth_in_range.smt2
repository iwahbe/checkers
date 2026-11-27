(set-logic ALL)
(assert (not (and (= (seq.nth (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)) 0) 1) (= (seq.nth (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)) 2) 3) (= (seq.len (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))) 3))))
(check-sat)
