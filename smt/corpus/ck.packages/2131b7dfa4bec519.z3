;; work 719
sat
((|name#1| (seq.unit 2))
 (|nodes#0| (std.prelude.Cons (ck.packages.Node (seq.unit 4)
                                    (seq.unit 5)
                                    (ck.manifest.PinnedPath (seq.unit 7))
                                    (ck.manifest.Manifest
                                      (seq.unit 3)
                                      (ck.manifest.Version 8 9 10)
                                      (as std.prelude.Nil
                                          (std.prelude.List ck.manifest.Dep)))
                                    (seq.unit 6))
                  (as std.prelude.Nil (std.prelude.List ck.packages.Node))))
 (|o#2| (as seq.empty (Seq Int))))
