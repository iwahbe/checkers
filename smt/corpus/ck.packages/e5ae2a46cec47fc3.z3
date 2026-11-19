;; work 1018
sat
((|todo#1| (let ((a!1 (ck.packages.Need (ck.manifest.Dep (seq.unit 2)
                                              (ck.manifest.Path (seq.unit 7)))
                             (seq.unit 3)
                             (seq.unit 4))))
  (std.prelude.Cons a!1
                    (as std.prelude.Nil (std.prelude.List ck.packages.Need)))))
 (|nodes#2| (std.prelude.Cons (ck.packages.Node (as seq.empty (Seq Int))
                                    (as seq.empty (Seq Int))
                                    (ck.manifest.PinnedPath
                                      (as seq.empty (Seq Int)))
                                    (ck.manifest.Manifest
                                      (as seq.empty (Seq Int))
                                      (ck.manifest.Version 3 3 3)
                                      (as std.prelude.Nil
                                          (std.prelude.List ck.manifest.Dep)))
                                    (as seq.empty (Seq Int)))
                  (as std.prelude.Nil (std.prelude.List ck.packages.Node))))
 (|lock#3| (std.prelude.Cons (ck.manifest.Locked
                    (as seq.empty (Seq Int))
                    (ck.manifest.PinnedPath (as seq.empty (Seq Int))))
                  (as std.prelude.Nil (std.prelude.List ck.manifest.Locked))))
 (|c#4| (ck.packages.Caps std.files.Fs!val!0
                  std.system.Env!val!0
                  std.system.Proc!val!0
                  std.terminal.Term!val!0)))
