# cursor.ck — a parsed value and the position just after it.
module cursor

export record Parsed a src start : a~Type, src~Bytes, start~Nat
    value~a
    stop~Nat, start < stop, stop <= len src
