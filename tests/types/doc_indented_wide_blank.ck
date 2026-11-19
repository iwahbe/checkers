# A line of a code block that is only white space is blank, whatever the
# white space: two full-width spaces (U+3000, three bytes each) are wider
# than the indentation cut off the block's lines.
module doc_indented_wide_blank

# Between lines of the block, and after it:
#
#     check 1 + 1 == 2
# 　　
#     check 2 + 2 == 4
# 　　
export fn twice n -> r : n~Nat, r~Nat
    n + n
