;; work 1375
sat
((|name#1| (seq.unit 3))
 (|nodes#0| (std.prelude.Cons (ck.packages.Node (seq.unit 3)
                                    (seq.unit 4)
                                    (ck.manifest.PinnedPath (seq.unit 10))
                                    (ck.manifest.Manifest
                                      (seq.unit 2)
                                      (ck.manifest.Version 12 13 14)
                                      (as std.prelude.Nil
                                          (std.prelude.List ck.manifest.Dep)))
                                    (seq.unit 5))
                  (as std.prelude.Nil (std.prelude.List ck.packages.Node)))))
