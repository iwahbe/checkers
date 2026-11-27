sat
((ys (let ((a!1 (Cons (seq.++ (seq.unit 1) (seq.unit 2))
                 (Cons (seq.unit 3) (Cons (seq.unit 4) Nil)))))
  (Cons (seq.++ (seq.unit 1) (seq.unit 2))
        (Cons (seq.++ (seq.unit 1) (seq.unit 2)) a!1))))
 (xs (Cons (seq.++ (seq.unit 1) (seq.unit 2))
      (Cons (seq.unit 3) (Cons (seq.unit 4) Nil)))))
