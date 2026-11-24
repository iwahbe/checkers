module template_errors

let UNCLOSED = tag"a{x"
let CLOSE = tag"a}b"
let COLON = tag"{x: Hex}"
let EMPTY_OPTIONS = tag"{x |}"
let TWO = tag"{x, y}"
let COMMENT = tag"{x # y}"
let BAD_OPTION = tag"{x | Hex Hex,}"
