(set-logic ALL)
; Z3 prints a constant the query defines, with its value: it is read, and
; must be what the definition gives: here it is not. (The answer is edited.)
(define-funs-rec ((k () Int)) ((+ 1 2)))
(declare-const x Int)
(assert (= x k))
(assert (not false))
(check-sat)
