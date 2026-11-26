;; work 1680
sat
((|package#1| (seq.unit 2))
 (|ms#3| (std.prelude.Cons (doc.Module (seq.unit 6)
                              (seq.unit 7)
                              (as std.prelude.Nil (std.prelude.List doc.Import))
                              (as std.prelude.Nil (std.prelude.List doc.Item))
                              (seq.unit 8)
                              (as std.prelude.Nil (std.prelude.List (Seq Int))))
                  (as std.prelude.Nil (std.prelude.List doc.Module))))
 (|out#0| (seq.unit 3))
 (|root#4| (seq.unit 4))
 (|label#5| (seq.unit 5))
 (|cx#6| (let ((a!1 ((as const
                (Array (Seq Int)
                       (Array (Seq Int)
                              (Array Bool (std.prelude.Option (Seq Int))))))
             ((as const
                  (Array (Seq Int) (Array Bool (std.prelude.Option (Seq Int)))))
               ((as const (Array Bool (std.prelude.Option (Seq Int))))
                 (std.prelude.Some (as seq.empty (Seq Int))))))))
  (ck.literate.Context
    (as std.prelude.Nil (std.prelude.List ck.literate.Symbol))
    (as std.prelude.Nil (std.prelude.List (Tuple2 (Seq Int) (Seq Int))))
    (as seq.empty (Seq Int))
    (ck.literate.Compiler
      (as seq.empty (Seq Int))
      (as seq.empty (Seq Int))
      (as std.prelude.Nil (std.prelude.List (Seq Int))))
    a!1
    (as std.prelude.None
        (std.prelude.Option (Tuple2 (Seq Int) (std.prelude.List (Seq Int))))))))
 (|ts#2| (as std.prelude.Nil (std.prelude.List doc.Target)))
 (|fs#7| std.files.Fs!val!0)
 (|p#8| std.system.Proc!val!0))
