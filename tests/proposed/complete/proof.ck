module proof

import std.list

lemma length_nonneg xs : xs~List Int
    ensures list.length xs >= 0
    proof
        match xs
            []        -> auto
            _ :: rest -> ‸

# In a `proof` block, an arm's body.
# Keywords: `have`, `auto`, `admit`, `let`, `match`, `if`.
# Names: rest : List Int, xs : List Int, length_nonneg (for `have
# length_nonneg rest`), list (the module), and the prelude's names.
# Lemmas first after `have ‸`: length_nonneg, then the prelude's lemmas
# (refl, …) and `list.` for std.list's.
