module instance_deep

# An instance's context is found however deeply the type nests: `Ord`
# at 40 `Option`s.

fn less a b -> r : a~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option Int))))))))))))))))))))))))))))))))))))))), b~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Int)))))))))))))))))))))))))))))))))))))))), r~Bool
    a < b
