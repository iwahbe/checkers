module class_alias_deep_result

# A class used at a refinement alias whose function gives the class's
# type inside 20 `Option`s: the instance's values there must be of the
# alias.

class Plain t
    fn plain u -> r : u~Int, r~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option t)))))))))))))))))))

instance Plain Int
    fn plain u
        Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some u)))))))))))))))))))

fn used -> r : r~Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Nat))))))))))))))))))))
    plain 1
