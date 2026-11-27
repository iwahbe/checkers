;; work 1055
sat
((|#name#1| (seq.unit 2))
 (|#ps#0| (|#std.prelude.Cons|
  (|#ck.packages.Package|
    (seq.unit 3)
    (seq.unit 4)
    (as |#std.prelude.Nil| (|#std.prelude.List| (Seq Int)))
    (|#ck.manifest.PinnedPath| (seq.unit 8)))
  (as |#std.prelude.Nil| (|#std.prelude.List| |#ck.packages.Package|)))))
