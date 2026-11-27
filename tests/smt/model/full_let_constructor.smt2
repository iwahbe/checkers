(set-logic ALL)
; A `let` binding a constructor of a datatype with parameters that only
; its use in the body fixes: it is checked at that sort.
(declare-datatypes ((R 2)) ((par (T E) ((Good (val T)) (Bad (err E))))))
(declare-datatypes ((W 0)) (((w (w0 (R (Seq Int) Int)) (w1 (R (Seq Int) Int)) (w2 (R (Seq Int) Int))))))
(declare-const a W)
(assert (= (w0 a) ((as Good (R (Seq Int) Int)) (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3) (seq.unit 4) (seq.unit 5) (seq.unit 6) (seq.unit 7) (seq.unit 8)))))
(assert (= (w1 a) (w0 a)))
(assert (= (w2 a) (w0 a)))
(assert (not false))
(check-sat)
