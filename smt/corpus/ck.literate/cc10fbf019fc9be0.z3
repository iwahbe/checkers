;; work 4161
sat
((|s#1| (let ((a!1 (seq.++ (seq.unit 99)
                   (seq.unit 111)
                   (seq.unit 109)
                   (seq.unit 112)
                   (seq.unit 105)
                   (seq.unit 108)
                   (seq.unit 101)
                   (seq.unit 95)
                   (seq.unit 102)
                   (seq.unit 97)
                   (seq.unit 105)
                   (seq.unit 108))))
  (ck.literate.Sample
    a!1
    a!1
    a!1
    (as std.prelude.Nil (std.prelude.List (Tuple2 (Seq Int) Int)))
    a!1)))
 (|c#0| (ck.literate.Compiler
  (as seq.empty (Seq Int))
  (as seq.empty (Seq Int))
  (as std.prelude.Nil (std.prelude.List (Seq Int)))))
 (|all#2| (as seq.empty (Seq Int)))
 (|p#4| std.system.Proc!val!0))
