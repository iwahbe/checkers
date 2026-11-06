module refined_fn_gain

# D71c, unchanged by M10: no refinement at all can't gain one.

type Big = n~Int, n >= 5

fn gain xs -> ys : xs~List Int, ys~List Big
    xs                                          # error E0262: `List Int` is not `List Big`
