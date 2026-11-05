# bytes.ck — immutable byte strings.
module bytes

export fn matches_at src i word -> r : src~Bytes, i~Nat, word~Bytes, r~Bool,
                                       r implies i + len word <= len src
    __builtin
