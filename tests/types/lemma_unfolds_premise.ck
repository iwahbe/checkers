# A lemma that follows from one unfolding of its premise is proved,
# though Z3 could unfold the goal's recursive function without end.
module lemma_unfolds_premise

fn walk xs -> r : xs~List Int, r~Result Unit Int
    match xs
        []        -> Ok ()
        _ :: rest -> walk rest

fn by_try xs -> r : xs~List Int, r~Result Unit Int
    let _ = try walk xs
    Ok ()

lemma walked xs : xs~List Int, by_try xs == Ok ()
    ensures walk xs == Ok ()
