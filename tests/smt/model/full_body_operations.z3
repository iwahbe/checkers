;; edited: Z3 printed `h`, `k` and `g` as constants and an `ite` on `none`; each body uses the operations instead
sat
(
  (define-fun h ((x!0 B)) Int
    (ite (is-mk x!0) (un x!0) 0))
  (define-fun k ((x!0 (Array Int Int))) Int
    (select x!0 3))
  (define-fun g ((x!0 (Seq Int))) Int
    (+ (seq.len x!0) (seq.nth x!0 0) (div 7 2) (mod 7 2)))
)
