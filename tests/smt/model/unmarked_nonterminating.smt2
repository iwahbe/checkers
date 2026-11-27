(set-logic ALL)
; `g x = g x + 1` has no solution, so no model satisfies this query; a
; definition not marked terminating can't be part of a counterexample, even
; where no assertion reaches it.
; Z3 5.3.3 answers `sat` here; by SMT-LIB 2.6 §4.2.3 (note 4) the query is
; unsatisfiable, and `refutes` follows SMT-LIB.
(define-fun-rec g ((x Int)) Int (+ (g x) 1))
(assert (not false))
(check-sat)
