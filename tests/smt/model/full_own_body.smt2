(set-logic ALL)
; Z3 prints the query's own constants and named assertions as bodies, in
; the query's operations (`seq.extract`, a tester): each is read, and
; must be what the query gives it.
(declare-datatypes ((O 1)) ((par (T) ((none) (some (val T))))))
(declare-const s (Seq Int))
(declare-const o (O Int))
(define-funs-rec ((k () (Seq Int))) ((seq.extract s 1 2)))
(define-funs-rec ((e () Bool)) ((is-none o)))
(assert (! (= (seq.len k) 2) :named a1))
(assert (! (is-none o) :named a2))
(assert (= (seq.len s) 5))
(assert (not false))
(check-sat)
