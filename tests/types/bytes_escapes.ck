module bytes_escapes

import std.string

# A bytes literal takes a string's escapes, plus `\xNN` for any byte: `\u{…}`
# is the character's UTF-8 bytes whatever its value, as in a string.

check b"\u{e9}" == b"\xc3\xa9"
check b"\u{e9}" == string.bytes "é"
check b"\u{7f}" == b"\x7f"
check b"\u{100}" == b"\xc4\x80"
check b"\xe9" != b"\u{e9}"
