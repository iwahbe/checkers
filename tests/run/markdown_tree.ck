# markdown_tree.ck — std.markdown's syntax tree for a small document: each
# block's and inline's span, shown as the source text it covers (#640 a).

module tree

import std.system (System, ExitCode)
import std.terminal
import std.markdown (Block, Inline, Span, Item, Paragraph, Heading, ThematicBreak, Quote, Bullets, Numbered, Code, Html,
                     Text, CodeSpan, Emph, Strong, Link, Image, RawHtml, SoftBreak, HardBreak)
import std.markdown
import std.string
import std.bytes
import std.list
import std.string (debug)

let SRC = "# Title *x*\n\n> quote\n> - a [b] `c` [nope]\n>   more\n\n```checkers\nfn f\n  x\n```\n\n    indented\n\n[b]: /url\n\t- tab item  \n  next\n"

fn slice s -> r : s~Span, r~String
    let b = string.bytes SRC
    if s.start <= s.stop and s.stop <= len b
        match string.from_utf8 (bytes.slice b s.start s.stop)
            Some t -> debug t
            None   -> "?"
    else
        "bad " ++ debug s.start ++ ".." ++ debug s.stop

fn ind n -> r : n~Nat, r~String
    if n == 0 then "" else "  " ++ ind (n - 1)

fn blocks bs n -> r : bs~List Block, n~Nat, r~String
    match bs
        b :: rest -> block b n ++ blocks rest n
        []        -> ""

fn items is n -> r : is~List Item, n~Nat, r~String
    match is
        Item bs s :: rest -> ind n ++ "item " ++ slice s ++ "\n" ++ blocks bs (n + 1) ++ items rest n
        []                -> ""

fn block b n -> r : b~Block, n~Nat, r~String
    match b
        Paragraph xs s      -> ind n ++ "para " ++ slice s ++ "\n" ++ inlines xs (n + 1)
        Heading l xs s      -> ind n ++ "h" ++ debug l ++ " " ++ slice s ++ "\n" ++ inlines xs (n + 1)
        ThematicBreak s     -> ind n ++ "hr " ++ slice s ++ "\n"
        Quote bs s          -> ind n ++ "quote " ++ slice s ++ "\n" ++ blocks bs (n + 1)
        Bullets t is s      -> ind n ++ "bullets " ++ debug t ++ " " ++ slice s ++ "\n" ++ items is (n + 1)
        Numbered st t is s  -> ind n ++ "numbered " ++ slice s ++ "\n" ++ items is (n + 1)
        Code info text ls s -> ind n ++ "code " ++ debug info ++ " " ++ slice s ++ " lines " ++ string.concat (list.map slice ls) ++ "\n"
        Html t s            -> ind n ++ "html " ++ slice s ++ "\n"

fn inlines xs n -> r : xs~List Inline, n~Nat, r~String
    match xs
        x :: rest -> inline x n ++ inlines rest n
        []        -> ""

fn inline x n -> r : x~Inline, n~Nat, r~String
    match x
        Text t s         -> ind n ++ "text " ++ debug t ++ " " ++ slice s ++ "\n"
        CodeSpan t s     -> ind n ++ "code " ++ slice s ++ "\n"
        Emph xs s        -> ind n ++ "emph " ++ slice s ++ "\n" ++ inlines xs (n + 1)
        Strong xs s      -> ind n ++ "strong " ++ slice s ++ "\n" ++ inlines xs (n + 1)
        Link t xs ref s  -> ind n ++ "link " ++ t.url ++ " " ++ debug ref ++ " " ++ slice s ++ "\n" ++ inlines xs (n + 1)
        Image t xs ref s -> ind n ++ "image " ++ slice s ++ "\n"
        RawHtml t s      -> ind n ++ "rawhtml " ++ slice s ++ "\n"
        SoftBreak s      -> ind n ++ "soft " ++ slice s ++ "\n"
        HardBreak s      -> ind n ++ "hard " ++ slice s ++ "\n"

fn def x -> r : x~markdown.Definition, r~(String, String)
    (x.label, slice x.span)

fn refr x -> r : x~markdown.Reference, r~(String, String)
    (x.label, slice x.span)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let d = markdown.parse SRC
    terminal.write (blocks d.blocks 0) sys.term
    terminal.print_line (debug (list.map def d.definitions)) sys.term
    terminal.print_line (debug (list.map refr d.unresolved)) sys.term
    Success
