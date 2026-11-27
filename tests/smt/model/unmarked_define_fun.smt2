(set-logic ALL)
; A `define-fun` needs no termination mark: `refutes` runs it as its body
; without `--terminating`.
(define-fun p ((n Int)) Int (+ n 1))
(declare-const x Int)
(assert (= (p x) 2))
(assert (not false))
(check-sat)
(get-value (x))
