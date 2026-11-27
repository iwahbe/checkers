;; work 9468
sat
((|#todo#1| (let ((a!1 (|#ck.packages.Need|
             (|#ck.manifest.Dep|
               (seq.unit 8)
               (|#ck.manifest.Path| (seq.unit 8)))
             (seq.unit 8)
             (seq.unit 8))))
  (|#std.prelude.Cons|
    a!1
    (as |#std.prelude.Nil| (|#std.prelude.List| |#ck.packages.Need|)))))
 (|#nodes#2| (as |#std.prelude.Nil| (|#std.prelude.List| |#ck.packages.Node|)))
 (|#lock#3| (as |#std.prelude.Nil| (|#std.prelude.List| |#ck.manifest.Locked|)))
 (|#c#4| (|#ck.packages.Caps|
  |#std.files.Fs!val!0|
  |#std.system.Env!val!0|
  |#std.system.Proc!val!0|
  |#std.terminal.Term!val!0|))
 (|#root#0| (seq.unit 8)))
