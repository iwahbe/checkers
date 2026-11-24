# A heading's level is 1 to 6: a `Heading` with any other level is
# rejected, and the parser gives levels 1 to 6.
module markdown_heading_level

import std.markdown (Block, Heading, Paragraph, Span)
import std.markdown

fn at n -> b : n~Nat, b~Block
    Heading n [] (Span 0 0)

fn seven -> b : b~Block
    Heading 7 [] (Span 0 0)

fn zero -> b : b~Block
    Heading 0 [] (Span 0 0)

fn one -> b : b~Block
    Heading 1 [] (Span 0 0)

fn six -> b : b~Block
    Heading 6 [] (Span 0 0)

fn checked n -> b : n~Nat, b~Block
    if n >= 1 and n <= 6 then Heading n [] (Span 0 0) else Paragraph [] (Span 0 0)

fn level text -> r : text~String, r~Nat
    match (markdown.parse text).blocks
        Heading n _ _ :: _ -> n
        _                  -> 0

check level "# a" == 1
check level "###### a" == 6
check level "####### a" == 0
check level "a\n=" == 1
check level "a\n-" == 2
