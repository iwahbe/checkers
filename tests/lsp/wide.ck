module wide

# Text before the error is wider in bytes than in UTF-16 code units.
fn f -> r : r~String
    "é😀" ++ 1
