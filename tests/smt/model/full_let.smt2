(set-logic ALL)
; Z3 shares a repeated subterm of a value with `let`.
(declare-datatypes ((Lst 1)) ((par (T) ((none) (more (first T) (rest (Lst T)))))))
(declare-const xs (Lst (Lst (Seq Int))))
(declare-const ys (Lst (Seq Int)))
(assert (= ys ((as more (Lst (Seq Int))) (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3)) ((as more (Lst (Seq Int))) (seq.++ (seq.unit 4) (seq.unit 5)) (as none (Lst (Seq Int)))))))
(assert (= xs ((as more (Lst (Lst (Seq Int)))) ys ((as more (Lst (Lst (Seq Int)))) ys (as none (Lst (Lst (Seq Int))))))))
(assert (not false))
(check-sat)
