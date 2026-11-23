module signature_match

# Laid out already: unchanged.
class Peel s
    fn peel xs -> r : xs~s, r~Option s,
                      match r
                          None   -> True
                          Some y -> True

# Arms go one level in from `match`, aligned; the body one level in from `fn`.
fn pick o -> r : o~Option Int, r~Int,
                 match o
                   None -> r == 0
                   Some x -> r == x
      match o
          None -> 0
          Some x -> x
