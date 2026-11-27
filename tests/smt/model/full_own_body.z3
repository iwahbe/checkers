sat
(
  (define-fun o () (O Int)
    none)
  (define-fun s () (Seq Int)
    (seq.++ (seq.unit 6) (seq.unit 7) (seq.unit 8) (seq.unit 19) (seq.unit 18)))
  (define-fun a1 () Bool
    (= (seq.len k) 2))
  (define-fun e () Bool
    (is-none o))
  (define-fun k () (Seq Int)
    (seq.extract s 1 2))
  (define-fun a2 () Bool
    (is-none o))
)
