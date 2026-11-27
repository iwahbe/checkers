;; work 2040
sat
((|#name#1| (seq.unit 3))
 (|#nodes#0| (|#std.prelude.Cons|
  (|#ck.packages.Node|
    (seq.unit 3)
    (seq.unit 4)
    (|#ck.manifest.PinnedPath| (seq.unit 14))
    (|#ck.manifest.Manifest|
      (seq.unit 2)
      (|#ck.manifest.Version| 17 18 19)
      (as |#std.prelude.Nil| (|#std.prelude.List| |#ck.manifest.Dep|)))
    (seq.unit 5))
  (as |#std.prelude.Nil| (|#std.prelude.List| |#ck.packages.Node|))))
 (|#best#2| (|#std.prelude.Some|
  (|#ck.packages.Node|
    (seq.unit 11)
    (seq.unit 12)
    (|#ck.manifest.PinnedPath| (seq.unit 16))
    (|#ck.manifest.Manifest|
      (seq.unit 10)
      (|#ck.manifest.Version| 23 24 25)
      (as |#std.prelude.Nil| (|#std.prelude.List| |#ck.manifest.Dep|)))
    (seq.unit 13)))))
