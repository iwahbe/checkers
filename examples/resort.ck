# resort.ck — using a verified library through its interface (SPEC §6, M4).
#
# `sort`'s body is sealed inside `sort.ck`: here the prover knows only its
# postconditions (`sorted ys`, `perm xs ys`) and the lemmas `sort.ck`
# exports. Showing that sorting twice is the same as sorting once needs the
# lemma `sort_of_sorted`; without the `have`, it can't be proven.

module resort

import sort (sort)

export fn sort_twice xs -> ys : xs~List Int, ys~List Int, ys == sort xs
    have sort.sort_of_sorted (sort xs)
    sort (sort xs)

check sort_twice [2, 3, 1] == [1, 2, 3]
