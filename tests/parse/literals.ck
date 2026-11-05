module literals

let BYTES = ['a', '"', '\'', '\\', '\n', '\x7f']
let CHARS = [c'a', c'é', c'\u{1F600}', c'\'']
let STRINGS = ["", "'", "say \"hi\"", "caf\u{e9}", "tab\there"]
let RAW = b"\x00\xff\\u"
let NUMBERS = [0, 42, 1_000_000, 0xFF, 0x7f]
