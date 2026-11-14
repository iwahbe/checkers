module proof

# In a proof (D142): `auto`, `admit` and lemmas.
import std.list

lemma length_nonneg xs : xs~List Int
    ensures list.length xs >= 0
    proof
        match xs
            []        -> auto
            _ :: rest -> ‸

# After `have`: lemmas only, and classes for their lemmas.
lemma twice xs : xs~List Int
    ensures list.length xs >= 0
    proof
        have ‸
