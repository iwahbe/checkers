;; work 942
sat
((|ps#0| (std.prelude.Cons (ck.packages.Package
                    (seq.unit 2)
                    (seq.unit 3)
                    (as std.prelude.Nil (std.prelude.List (Seq Int)))
                    (ck.manifest.PinnedPath (seq.unit 7)))
                  (as std.prelude.Nil (std.prelude.List ck.packages.Package)))))
