module post_block

# A postcondition that is a `match`: shown as written, without the comment
# after it.
export fn pick o -> r : o~Option Nat, r~Nat,
                        match o
                            None   -> r == 0
                            Some n -> r == n
                            # Not part of the postcondition.
    1
