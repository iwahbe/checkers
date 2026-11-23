module class_type_pre

# A class's type in a precondition's predicate.

class Display a
    type Options
    fn valid os -> b : os~List Options, b~Bool
    fn display x os -> s : x~a, os~List Options, valid os, s~String

record Money
    cents~Int

enum MoneyOption
    Cents
    Whole

instance Display Money
    type Options = MoneyOption
    fn valid os
        len os <= 1
    fn display m os
        "m"

record Pair a
    first~a
    second~a

instance Display (Pair a) : Display a
    type Options = Display.Options a
    fn valid os
        Display.valid os
    fn display p os
        Display.display p.first os ++ Display.display p.second os

fn met -> s : s~String
    display (Money 1) [Cents]

fn met_through_context -> s : s~String
    display (Pair (Money 1) (Money 2)) [Whole]

fn passed x os -> s : Display a, x~a, os~List (Display.Options a), Display.valid os, s~String
    display x os

fn not_met -> s : s~String
    display (Money 1) [Cents, Whole]
