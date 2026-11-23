module reused_definition_recognizer

# A recursive function whose `match` tests an `Option` of a tuple, used by a
# first proof and again by later ones: they get the solver's answer too.

fn within rest xs -> b : Seq s, rest~s, xs~s, b~Bool
    decreasing Seq.size xs
    match Seq.uncons xs
        None         -> rest == xs
        Some (_, ys) -> rest == xs or within rest ys

fn first_use xs -> r : Seq s, xs~s, r~s, within r xs
    xs

class Step s
    fn step xs -> r : xs~s, r~s

fn checked xs -> r : Seq s, Step s, xs~s, r~s, within r xs
    let ys = Step.step xs
    if within ys xs then ys else xs

fn unchecked xs -> r : Seq s, Step s, xs~s, r~s, within r xs
    Step.step xs
