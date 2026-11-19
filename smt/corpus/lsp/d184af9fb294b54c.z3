;; work 613
sat
((|g#0| 0)
 (|root#1| (seq.unit 2))
 (|sh#4| (lsp.Shared (std.prelude.Cons (lsp.Root (as seq.empty (Seq Int))
                                        (- 1)
                                        false
                                        (as std.prelude.Nil
                                            (std.prelude.List lsp.Diag))
                                        (as std.prelude.Nil
                                            (std.prelude.List lsp.Diag)))
                              (as std.prelude.Nil (std.prelude.List lsp.Root)))
            (as std.prelude.Nil (std.prelude.List lsp.Entry))
            (as std.prelude.Nil (std.prelude.List lsp.Pending)))))
