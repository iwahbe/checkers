;; work 7430
sat
((|args#0| (std.prelude.Cons (seq.++ (seq.unit 45) (seq.unit 111))
                  (std.prelude.Cons (seq.++ (seq.unit 45) (seq.unit 111))
                                    (std.prelude.Cons (seq.unit 45)
                                                      (as std.prelude.Nil
                                                          (std.prelude.List (Seq Int)))))))
 (|fs#3| std.files.Fs!val!0)
 (|ckc#1| (seq.unit 111))
 (|p#4| std.system.Proc!val!0)
 (|term#2| std.terminal.Term!val!0))
