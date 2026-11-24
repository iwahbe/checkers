(set-logic ALL)
; Non-uniform recursion: `nnil` is a value of every `N A`. Accepted.
(declare-datatypes ((N 1)) ((par (A) ((nnil) (ncons (h A) (t (N (N A))))))))
(declare-const c (N Int))
(assert (not false))
(check-sat)
