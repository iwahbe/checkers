module templates

let NAMED = tag"a{x}b"
let OPTIONS = tag"{x | Hex, Width 4}"
let POSITIONAL = tag"{}, {}"
let POSITIONAL_OPTIONS = tag"{| Hex}"
let QUALIFIED = app.page"<p>{name}</p>"
let BRACES = tag"{{x}} {{{x}}}"
let BRACKETS = tag"{f (g [1, 2]) [(y)]}"
let STRING_IN_HOLE = tag"{f "a{b}"}"
let NESTED = tag"{inner"{x}"}"
let CONS_IN_HOLE = tag"{x :: xs}"
let PIPE_IN_TEMPLATE = tag"{inner"{x | A}" | B}"
let ESCAPES = tag"\"{x}\n\u{e9}"
let APPLIED = f tag"{x}" y
let SPACED = tag "{x}"
let KEYWORD = if c then"{x}" else"{y}"
