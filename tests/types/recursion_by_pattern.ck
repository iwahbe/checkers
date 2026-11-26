# A recursive function whose `match` is on a sequence pattern is unfolded
# one case at a time: a fact about it doesn't send the prover unfolding it
# without end. A wrong lemma has a counterexample, and a proof doesn't
# depend on the order of its facts.
module recursion_by_pattern

fn pow n k -> r : n~Int, k~Nat, r~Int, n >= 0 implies r >= 0, n > 0 implies r > 0
    decreasing k
    if k == 0 then 1 else n * pow n (k - 1)

# `ys` is what is left of `xs` after some of its first bytes.
fn suffix ys xs -> r : ys~Bytes, xs~Bytes, r~Bool
    match xs
        _ :: rest -> ys == xs or suffix ys rest
        []        -> ys == xs

lemma suffix_len ys xs : ys~Bytes, xs~Bytes, suffix ys xs
    ensures len ys <= len xs
    proof
        decreasing len xs
        match xs
            _ :: rest ->
                if ys == xs
                    auto
                else
                    have suffix_len ys rest
            []        -> auto

lemma within_pow_first ys xs f : ys~Bytes, xs~Bytes, f~Nat, suffix ys xs, len xs < pow 10 f
    ensures len ys < pow 10 f
    proof
        have pow 10 f > 0
        have suffix_len ys xs

lemma within_pow_last ys xs f : ys~Bytes, xs~Bytes, f~Nat, suffix ys xs, len xs < pow 10 f
    ensures len ys < pow 10 f
    proof
        have suffix_len ys xs
        have pow 10 f > 0

# Wrong: `ys` may be shorter.
lemma same ys xs : ys~Bytes, xs~Bytes, suffix ys xs
    ensures ys == xs
