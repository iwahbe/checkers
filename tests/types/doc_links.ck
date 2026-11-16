# doc_links.ck — doc comments' links and code (D148 e): [twice], [`Pt`],
# [Pt.x], [`std.list`], [Option] and [Some] resolve; [nothing] and
# [list.nope] don't (W030); [helper] isn't exported (W031); [x, y], [0] and
# `[code]` aren't links, nor is [a link](https://example.com), and [defined]
# has a definition.
#
# [defined]: https://example.com
#
# ```
# #! import doc_links
# check doc_links.twice 2 == 4
# ```
module doc_links

import std.list

# A point, with [list.length] in scope.
export record Pt
    x~Nat
    y~Nat

# Twice `n`.
#
# ```checkers,compile_fail,E0201
# #! import doc_links
# check doc_links.twice "a" == 1
# ```
#
# ```checkers,compile_fail
# check 1 + 1 == 2
# ```
#
# ```checkers,compile_fail,E0201
# check 1 - 2 == 0
# ```
#
# ```
# check thrice 1 == 3
# ```
#
# ```checkers,ignore
# fn not checked
# ```
#
# ```sh
# not checkers
# ```
export fn twice n -> r : n~Nat, r~Nat
    helper n + helper n

fn helper n -> r : n~Nat, r~Nat
    n
