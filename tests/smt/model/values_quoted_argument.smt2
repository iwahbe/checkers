(set-logic ALL)
; `(f |1|)` is `f` at the symbol `|1|`, not at the numeral 1: it isn't
; the term asked, so the list is not read. (The answer is edited.)
(declare-fun f (Int) Int)
(assert (= (f 1) 5))
(assert (not false))
(check-sat)
(get-value ((f 1)))
