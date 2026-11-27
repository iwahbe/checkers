(set-logic ALL)
; A `let` binding a constructor of a datatype with parameters, without
; `as`: its sort is what its arguments make it, and a field whose sort is
; then known (`Nil` here) is checked at it.
(declare-datatypes ((L 1)) ((par (T) ((Nil) (Cons (hd T) (tl (L T)))))))
(declare-const xs (L (Seq Int)))
(declare-const ys (L (Seq Int)))
(assert (= xs ((as Cons (L (Seq Int))) (seq.++ (seq.unit 1) (seq.unit 2)) ((as Cons (L (Seq Int))) (seq.unit 3) ((as Cons (L (Seq Int))) (seq.unit 4) (as Nil (L (Seq Int))))))))
(assert (= ys ((as Cons (L (Seq Int))) (seq.++ (seq.unit 1) (seq.unit 2)) ((as Cons (L (Seq Int))) (seq.++ (seq.unit 1) (seq.unit 2)) xs))))
(assert (= (tl (tl ys)) xs))
(assert (not false))
(check-sat)
(get-value (ys xs))
