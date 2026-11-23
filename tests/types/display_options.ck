module display_options

# A type's own `Display` instance, with options of its own: they are
# accepted for it, alone and combined, and an option of another type is
# a type error at the option, in a call and in a template's hole.

import std.list
import std.string (Display, display, format, Hex)

record Money
    cents~Int

enum MoneyOption
    Cents
    Whole

instance Display Money
    type Options = MoneyOption
    fn display m os
        if list.contains os Cents then Display.display m.cents [] ++ "c" else "$" ++ Display.display (m.cents / 100) []

fn good m -> s : m~Money, s~String
    display m [] ++ display m [Cents] ++ format"{m | Whole, Cents}"

fn other_type m -> s : m~Money, s~String
    display m [Hex]

fn in_hole m -> s : m~Money, s~String
    format"{m | Cents, Hex}"

fn int_option n -> s : n~Int, s~String
    format"{n | Cents}"
