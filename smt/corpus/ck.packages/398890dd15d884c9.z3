;; work 620
sat
((|name#1| (seq.unit 3))
 (|nodes#0| (std.prelude.Cons (ck.packages.Node (seq.unit 2)
                                    (seq.unit 5)
                                    (ck.manifest.PinnedPath (seq.unit 7))
                                    (ck.manifest.Manifest
                                      (seq.unit 4)
                                      (ck.manifest.Version 8 9 10)
                                      (as std.prelude.Nil
                                          (std.prelude.List ck.manifest.Dep)))
                                    (seq.unit 6))
                  (as std.prelude.Nil (std.prelude.List ck.packages.Node)))))
