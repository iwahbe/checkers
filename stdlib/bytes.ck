# bytes.ck — immutable byte strings.
module std.bytes

export fn matches_at src i word -> r : src~Bytes, i~Nat, word~Bytes, r~Bool,
                                       r implies i + len word <= len src
    __builtin

# The bytes from `i` up to (not including) `j`.
export fn slice src i j -> r : src~Bytes, i~Nat, j~Nat, i <= j, j <= len src,
                               r~Bytes, len r == j - i
    __builtin

# The byte strings one after another, in time linear in the result.
export fn concat parts -> r : parts~List Bytes, r~Bytes
    __builtin
