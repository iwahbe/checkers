(set-logic ALL)
(assert (not (= (seq.++ (seq.unit 1) (as seq.empty (Seq Int)) (seq.++ (seq.unit 2) (seq.unit 3))) (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)))))
(check-sat)
