;; work 1354
sat
((|#name#1| (seq.unit 2))
 (|#nodes#0| (|#std.prelude.Cons|
  (|#ck.packages.Node|
    (seq.unit 4)
    (seq.unit 5)
    (|#ck.manifest.PinnedPath| (seq.unit 11))
    (|#ck.manifest.Manifest|
      (seq.unit 3)
      (|#ck.manifest.Version| 13 14 15)
      (as |#std.prelude.Nil| (|#std.prelude.List| |#ck.manifest.Dep|)))
    (seq.unit 6))
  (as |#std.prelude.Nil| (|#std.prelude.List| |#ck.packages.Node|)))))
