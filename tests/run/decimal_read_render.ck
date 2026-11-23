module decimal_read_render

# `decimal.parse_render` is trusted, like the primitives: reading what
# `render` writes gives the number back, whatever follows that can't
# continue a number. Here on numbers of every shape `render` writes (small,
# large, with an exponent, negative), each followed by every kind of byte.

import std.system (System, ExitCode)
import std.terminal
import std.decimal (Decimal)
import std.parse (Parsable)
import std.string
import std.utf8
import std.list

let MANTISSAS = [0, 1, -1, 7, -12, 10, 100, 123456789, -987654321, 5, 25, 99999999999999999999]

let EXPONENTS = [-30, -8, -7, -6, -3, -1, 0, 1, 2, 5, 21, 22, 23, 40, -9223372036854775809, 9223372036854775808]

let POSTS = [b"", b",", b"]", b"}", b" ", b"\n", b"x", b"-", b":"]

# The cases where reading the rendered number back fails.
fn failures ms -> r : ms~List Int, r~List String
    match ms
        []        -> []
        m :: rest -> by_exponent m EXPONENTS ++ failures rest

fn by_exponent m es -> r : m~Int, es~List Int, r~List String
    match es
        []        -> []
        e :: rest -> by_post (decimal.scaled m e) POSTS ++ by_exponent m rest

fn by_post d ps -> r : d~Decimal, ps~List Bytes, r~List String
    match ps
        []        -> []
        p :: rest ->
            let ok = Parsable.parse (utf8.encode (decimal.render d) ++ p) Decimal Int == Ok (d, p)
            if ok then by_post d rest else (decimal.render d ++ " " ++ string.debug p) :: by_post d rest

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    let bad = failures MANTISSAS
    let cases = list.length MANTISSAS * list.length EXPONENTS * list.length POSTS
    terminal.print_line (string.debug cases ++ " cases, " ++ string.debug (list.length bad) ++ " failures") term
    match bad
        [] -> Success
        _  ->
            terminal.print_line (string.concat (list.map (\l -> l ++ " ") bad)) term
            Failure 1
