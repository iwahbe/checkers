module refine_mult

# Only `own`, and only on a function type's parameter, may be written inside
# a type (E0123, D172 b).

fn ghost_param f -> r : f~(v~ghost a -> b), r~Unit
    ()

fn comptime_param f -> r : f~(v~comptime Int -> Int), r~Unit
    ()

fn own_result f -> r : f~(v~a -> w~own b), r~Unit
    ()

fn own_refinement n -> r : n~(m~own Int, m > 0), r~Unit
    ()

fn fine x f -> r : x~own a, f~own (v~own a -> b), r~b
    f x
