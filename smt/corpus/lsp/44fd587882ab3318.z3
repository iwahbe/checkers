;; work 511
sat
((|g#2| 0)
 (|root#3| (seq.unit 2))
 (|sh#7| (lsp.Shared (std.prelude.Cons (lsp.Root (as seq.empty (Seq Int))
                                        (- 1)
                                        false
                                        (as std.prelude.Nil
                                            (std.prelude.List lsp.Diag))
                                        (as std.prelude.Nil
                                            (std.prelude.List lsp.Diag)))
                              (as std.prelude.Nil (std.prelude.List lsp.Root)))
            (as std.prelude.Nil (std.prelude.List lsp.Entry))
            (as std.prelude.Nil (std.prelude.List lsp.Pending)))))
