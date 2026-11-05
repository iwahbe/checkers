module partial_given

import list

# A precondition about the arguments already given is checked right there.
fn div_by d x -> q : d~Int, d != 0, x~Int, q~Int
    x / d

fn halves xs -> ys : xs~List Int, ys~List Int
    list.map (div_by 2) xs

fn by_zero xs -> ys : xs~List Int, ys~List Int
    list.map (div_by 0) xs
