# An indented code block in a doc comment is code, as a fenced one with no
# language is (D162): compiled, with W032 for its errors. It can't carry
# attributes; a block that isn't Checkers needs a fence saying so.
module doc_indented

# One more than `n`:
#
#     #! import doc_indented (add1)
#     check add1 1 == 2
#
# Wrong, so reported:
#
#     #! import doc_indented (add1)
#     check add1 1 == "two"
#
# Not code: a paragraph's line, however indented, continues it,
#     like this one;
#
# - and a list item's text continues it at its own indentation:
#
#   still the item,
#
#   and four spaces in from the item's text is code:
#
#       check 1 + 1 == 2
export fn add1 n -> m : n~Nat, m~Nat
    n + 1
