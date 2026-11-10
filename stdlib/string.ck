# string.ck — UTF-8 strings (D20).
module std.string

export fn from_chars cs -> s : cs~List Char, s~String
    __builtin

export fn from_char c -> s : c~Char, s~String
    __builtin

export fn concat_map f s -> r : f~(Char -> String), s~String, r~String
    __builtin

export fn bytes s -> b : s~String, b~Bytes
    __builtin

# The strings one after another, in time linear in the result.
export fn concat parts -> s : parts~List String, s~String
    __builtin

# The bytes as a string, if they are UTF-8.
export fn from_utf8 b -> r : b~Bytes, r~Option String
    __builtin
