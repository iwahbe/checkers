(set-logic ALL)
; `(seq.++)` with no arguments is not SMT-LIB (Z3 refuses it): not read.
; (The answer is edited.)
(declare-const s (Seq Int))
(assert (= (seq.len s) 0))
(assert (not false))
(check-sat)
(get-value (s))
