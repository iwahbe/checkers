sat
(
  (define-fun xs () (Lst (Lst (Seq Int)))
    (let ((a!1 (more (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))
                 (more (seq.++ (seq.unit 4) (seq.unit 5))
                       (as none (Lst (Seq Int)))))))
  (more a!1 (more a!1 (as none (Lst (Lst (Seq Int))))))))
  (define-fun ys () (Lst (Seq Int))
    (more (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))
      (more (seq.++ (seq.unit 4) (seq.unit 5)) (as none (Lst (Seq Int))))))
)
