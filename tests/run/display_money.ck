module display_money

# A program's own `Display`, with options of its own, through `display`
# and through `format`'s holes.

import std.system (System, ExitCode)
import std.terminal
import std.string (Display, display, format)
import std.list

record Money
    cents~Int

export enum MoneyOption
    Cents                             # 1250¢
    Whole                             # $12, without cents

instance Display Money
    type Options = MoneyOption
    fn display m os
        if list.contains os Cents
            Display.display m.cents [] ++ "¢"
        else if list.contains os Whole
            "$" ++ Display.display (m.cents / 100) []
        else
            let c = m.cents % 100
            "$" ++ Display.display (m.cents / 100) [] ++ "." ++ (if c < 10 then "0" else "") ++ Display.display c []

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    let price = Money 1250
    terminal.print_line (display price []) t
    terminal.print_line (display (Money 1205) []) t
    terminal.print_line format"{price}" t
    terminal.print_line format"{price | Cents}" t
    terminal.print_line (format"{| Whole}" price) t
    Success
