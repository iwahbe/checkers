sat
(
  (define-fun b () (Seq Bool)
    (as seq.empty (Seq Bool)))
  (define-fun a () (Seq Int)
    (as seq.empty (Seq Int)))
  (define-fun seq.nth_u ((x!0 (Seq Int)) (x!1 Int)) Int
    7)
  (define-fun seq.nth_u ((x!0 (Seq Bool)) (x!1 Int)) Bool
    true)
)
