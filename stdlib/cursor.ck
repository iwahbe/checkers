# cursor.ck — a parsed value and the position just after it.
module std.cursor

# A value parsed from `src` starting at `start`, and where it stopped. A
# parse consumes at least one byte, so a parser that loops on `stop` ends.
export record Parsed a src start : a~Type, src~Bytes, start~Nat
    value~a
    stop~Nat, start < stop, stop <= len src
