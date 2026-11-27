(set-logic ALL)
; Z3 prints a `seq.nth_u` for each sort of sequence; each is read at its
; own sorts.
(declare-const a (Seq Int))
(declare-const b (Seq Bool))
(assert (= (seq.len a) 0))
(assert (= (seq.len b) 0))
(assert (= (seq.nth a 5) 7))
(assert (= (seq.nth b 3) true))
(assert (not false))
(check-sat)
