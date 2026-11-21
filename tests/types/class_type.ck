module class_type

import std.string (debug)

# A class's type: each instance gives it, or takes the class's default.

class Display a
    type Options = NoOptions
    fn display x os -> s : x~a, os~List Options, s~String

enum NoOptions

record Money
    cents~Int

enum MoneyOption
    Cents
    Whole

instance Display Money
    type Options = MoneyOption
    fn display m os
        match os
            [Cents] -> debug m.cents
            _       -> debug (m.cents / 100)

# Its `Options` is the default, `NoOptions`.
instance Display Int
    fn display x os
        debug x

record Pair a
    first~a
    second~a

# Its `Options` is its parts'.
instance Display (Pair a) : Display a
    type Options = Display.Options a
    fn display p os
        Display.display p.first os ++ Display.display p.second os

# At a known instance, the type is the instance's.
fn known -> s : s~String
    display (Money 1250) [Cents]

fn by_default -> s : s~String
    display 5 []

fn through_context -> s : s~String
    display (Pair (Money 1) (Money 2)) [Whole]

fn by_name -> os : os~List (Display.Options Money)
    [Cents]

fn matched os -> n : os~List (Display.Options Money), n~Int
    match os
        [Cents] -> 1
        _       -> 2

# At a type parameter: `[]`, or options it was given.
fn generic x -> s : Display a, x~a, s~String
    display x []

fn passed x os -> s : Display a, x~a, os~List (Display.Options a), s~String
    display x os ++ display x os

# The options are checked once `v`'s type is known.
fn later -> s : s~String
    (\v -> display v [Cents]) (Money 1250)
