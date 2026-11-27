(set-logic ALL)
; `((as nil L))` applies a constructor to no arguments, which Z3
; refuses: not read. (The answer is edited.)
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
(declare-const l L)
(assert (= l nil))
(assert (not false))
(check-sat)
(get-value (l))
