; A binder may hide an outer binder, as in Z3; the largest numbers options
; take; patterns that apply a constructor, a selector, a tester, `select`
; and a declared function, together mentioning every variable.
(set-option :rlimit 4294967295)
(set-option :timeout 4294967295)
(set-logic ALL)
(declare-datatypes ((D 0)) (((K (fd Int)) (L))))
(declare-fun p (Int) Bool)
(declare-const a (Array Int Int))
(assert (forall ((y Int)) (! (let ((y 2)) (p y)) :pattern ((p y)))))
(assert (forall ((d D) (y Int)) (! (> (fd d) (select a y)) :pattern ((fd d) (select a y)) :pattern ((is-K d) ((as K D) y)))))
(assert (not (p 2)))
(check-sat)
