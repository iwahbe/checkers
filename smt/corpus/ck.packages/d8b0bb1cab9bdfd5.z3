;; work 887
sat
((|n#0| (ck.packages.Need (ck.manifest.Dep (seq.unit 2)
                                   (ck.manifest.Git (seq.unit 5)
                                                    (ck.manifest.Version
                                                      0
                                                      7719
                                                      21238)))
                  (seq.unit 3)
                  (seq.unit 4)))
 (|lock#1| (std.prelude.Cons (ck.manifest.Locked
                    (as seq.empty (Seq Int))
                    (ck.manifest.PinnedPath (as seq.empty (Seq Int))))
                  std.prelude.Nil))
 (|c#2| (ck.packages.Caps std.files.Fs!val!0
                  std.system.Env!val!0
                  std.system.Proc!val!0
                  std.terminal.Term!val!0)))
