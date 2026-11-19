;; work 514
sat
((|todo#0| (std.prelude.Cons (seq.unit 2)
                  (as std.prelude.Nil (std.prelude.List (Seq Int)))))
 (|acc#2| (std.prelude.Cons (ck.packages.Package
                    (as seq.empty (Seq Int))
                    (as seq.empty (Seq Int))
                    (as std.prelude.Nil (std.prelude.List (Seq Int)))
                    (ck.manifest.PinnedPath (as seq.empty (Seq Int))))
                  (as std.prelude.Nil (std.prelude.List ck.packages.Package))))
 (|nodes#1| (std.prelude.Cons (ck.packages.Node (as seq.empty (Seq Int))
                                    (as seq.empty (Seq Int))
                                    (ck.manifest.PinnedPath
                                      (as seq.empty (Seq Int)))
                                    (ck.manifest.Manifest
                                      (as seq.empty (Seq Int))
                                      (ck.manifest.Version 2 2 2)
                                      (as std.prelude.Nil
                                          (std.prelude.List ck.manifest.Dep)))
                                    (as seq.empty (Seq Int)))
                  (as std.prelude.Nil (std.prelude.List ck.packages.Node)))))
