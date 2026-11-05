# string.ck — UTF-8 strings (D20).
module string

export fn from_chars cs -> s : cs~List Char, s~String
    __builtin

export fn from_char c -> s : c~Char, s~String
    __builtin

export fn concat_map f s -> r : f~(Char -> String), s~String, r~String
    __builtin

export fn bytes s -> b : s~String, b~Bytes
    __builtin
