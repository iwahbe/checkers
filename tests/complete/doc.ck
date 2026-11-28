# Completion in doc comments (#642 f): after `[`, a link's names: [tw‸
#
# ```
# #! import std.list
# check list.‸
# ```
module doc

export fn twice n -> r : n~Nat, r~Nat
    n + n
