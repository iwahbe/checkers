# Continuation lines (D92).
module continuation

fn sig_aligned a b -> r : a~Nat, b~Nat,
        r~Nat
    let xs = [ 1,
          2,
               3 ]
    let ys = list.map (\x ->
      x + 1) xs
    let zs = f (
            a,
                b
    )
    a + b
          + 1
