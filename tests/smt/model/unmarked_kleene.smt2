(set-logic ALL)
; The same, reached only under a conjunction that is false anyway.
; Z3 5.3.3 answers `sat` here; by SMT-LIB 2.6 §4.2.3 (note 4) the query is
; unsatisfiable, and `refutes` follows SMT-LIB.
(define-fun-rec g ((x Int)) Int (+ (g x) 1))
(assert (not (and (= (g 0) 0) false)))
(check-sat)
