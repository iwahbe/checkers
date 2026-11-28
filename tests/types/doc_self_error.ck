# A doc comment's example imports its module, whose error is reported once,
# at its own place:
#
#     check ONE == 1
module doc_self_error

export let ONE = 1

check ONE == 2
