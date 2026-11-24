# Two function parameters whose refinements mention a later parameter: each
# is checked against its own refinement, the second as well as the first.
module later_param_second_fn

fn both f g n -> r : f~(i~Int -> Int, i < n), g~(i~Int -> Int, i < n), n~Int, r~Int
    0

fn pass_both f g n -> r : f~(i~Int -> Int, i < n), g~(i~Int -> Int, i < n), n~Int, r~Int
    both f g n

# The refinements call a class's function (`Seq.size`).
fn both_sized f g xs -> r : Seq s, f~(ys~s -> Int, Seq.size ys < Seq.size xs),
                            g~(ys~s -> Int, Seq.size ys < Seq.size xs), xs~s, r~Int
    0

fn pass_both_sized f g xs -> r : Seq s, f~(ys~s -> Int, Seq.size ys < Seq.size xs),
                                 g~(ys~s -> Int, Seq.size ys < Seq.size xs), xs~s, r~Int
    both_sized f g xs

# `both_wide` may call `g` at `n`, which `pass_wide`'s `g` doesn't accept.
fn both_wide f g n -> r : f~(i~Int -> Int, i < n), g~(i~Int -> Int, i <= n), n~Int, r~Int
    0

fn pass_wide f g n -> r : f~(i~Int -> Int, i < n), g~(i~Int -> Int, i < n), n~Int, r~Int
    both_wide f g n

fn both_wide_sized f g xs -> r : Seq s, f~(ys~s -> Int, Seq.size ys < Seq.size xs),
                                 g~(ys~s -> Int, Seq.size ys <= Seq.size xs), xs~s, r~Int
    0

fn pass_wide_sized f g xs -> r : Seq s, f~(ys~s -> Int, Seq.size ys < Seq.size xs),
                                 g~(ys~s -> Int, Seq.size ys < Seq.size xs), xs~s, r~Int
    both_wide_sized f g xs
