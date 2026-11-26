;; work 2277
sat
((|todo#1| (let ((a!1 (ck.packages.Need (ck.manifest.Dep (seq.unit 2)
                                              (ck.manifest.Path (seq.unit 15)))
                             (seq.unit 3)
                             (seq.unit 4))))
  (std.prelude.Cons a!1
                    (as std.prelude.Nil (std.prelude.List ck.packages.Need)))))
 (|nodes#2| (as std.prelude.Nil (std.prelude.List ck.packages.Node)))
 (|lock#3| (as std.prelude.Nil (std.prelude.List ck.manifest.Locked)))
 (|c#4| (ck.packages.Caps std.files.Fs!val!0
                  std.system.Env!val!0
                  std.system.Proc!val!0
                  std.terminal.Term!val!0)))
