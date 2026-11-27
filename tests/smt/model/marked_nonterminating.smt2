(set-logic ALL)
; `main model` takes every definition as terminating unless `--unmarked`:
; with `g x = g x + 1` that promise is false, and `refutes` follows it. The
; mark is the caller's to keep (its form is a proposal), and `refutes` can't
; check it.
(define-fun-rec g ((x Int)) Int (+ (g x) 1))
(assert (not false))
(check-sat)
