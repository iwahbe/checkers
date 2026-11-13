# string.ck — UTF-8 strings (D20).
module std.string

import std.char
import std.list

# The characters, one after another.
export fn from_chars cs -> s : cs~List Char, s~String
    __builtin

# The one-character string.
export fn from_char c -> s : c~Char, s~String
    __builtin

# `f` applied to each character, the results one after another.
export fn concat_map f s -> r : f~(Char -> String), s~String, r~String
    concat (list.map f (chars s))

# The string's UTF-8 bytes.
export fn bytes s -> b : s~String, b~Bytes
    __builtin

# The strings one after another, in time linear in the result.
export fn concat parts -> s : parts~List String, s~String
    __builtin

# The bytes as a string, if they are UTF-8.
export fn from_utf8 b -> r : b~Bytes, r~Option String
    __builtin

# The characters of a string, in order (D119).
export fn chars s -> cs : s~String, cs~List Char
    __builtin

# ── Axioms about these builtins (D56, D119) ─────────────────────────────────
# A string is the characters it is made of, one after another. The prover
# sees a string as its UTF-8 bytes (§7.3), so these say how characters and
# bytes relate.

# No characters make the empty string.
export lemma from_chars_nil
    ensures from_chars [] == ""
    proof
        __builtin

# A string of characters is its first character, then the rest.
export lemma from_chars_cons c cs : c~Char, cs~List Char
    ensures from_chars (c :: cs) == from_char c ++ from_chars cs
    proof
        __builtin

# A string is made of its characters.
export lemma from_chars_chars s : s~String
    ensures from_chars (chars s) == s
    proof
        __builtin

# `concat` joins the strings with nothing between them.
export lemma concat_join parts : parts~List String
    ensures concat parts == list.join "" parts
    proof
        __builtin

# `concat_map` joins what `f` gives for each character.
export lemma concat_map_chars f s : f~(Char -> String), s~String
    ensures concat_map f s == list.join "" (list.map f (chars s))
    proof
        have concat_join (list.map f (chars s))

# One character's UTF-8 bytes: its code if it is ASCII, otherwise two to four
# bytes starting at 0xC2 or above.
export lemma from_char_bytes c : c~Char
    let b = bytes (from_char c)
    ensures len b > 0
        and (if char.code c < 128 then len b == 1 and b[0] == char.code c else b[0] >= 0xC2)
    proof
        __builtin

# The axioms on a few strings, against the builtins themselves.
check chars "aé€😀" == [c'a', c'é', c'€', c'😀']
check from_chars (chars "aé€😀") == "aé€😀"
check from_chars [] == "" and from_chars [c'é', c'x'] == from_char c'é' ++ from_chars [c'x']
fn dotted c -> s : c~Char, s~String
    from_char c ++ "."

check concat_map dotted "aé" == list.join "" (list.map dotted (chars "aé"))
check concat ["ab", "", "c"] == list.join "" ["ab", "", "c"] and concat [] == list.join "" []
check bytes (from_char c'A') == b"A" and bytes (from_char c'\u{80}') == b"\xC2\x80"
check bytes (from_char c'😀') == b"\xF0\x9F\x98\x80"
