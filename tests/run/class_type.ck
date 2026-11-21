module class_type

# A class's type at run time: each instance's options, and an array of a
# class's type made in generic code, laid out as the instance's type is.

import std.system (System, ExitCode)
import std.terminal
import std.array
import std.string (debug)

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
            [Cents] -> debug m.cents ++ "¢"
            _       -> "$" ++ debug (m.cents / 100)

instance Display Int
    fn display x os
        debug x

class Packed a
    type Elem
    fn elem x -> e : x~a, e~Elem

instance Packed Int
    type Elem = U8
    fn elem x
        200

instance Packed Bool
    type Elem = String
    fn elem x
        "yes"

fn row x n -> r : Packed a, x~a, n~Nat, r~Array (Packed.Elem a), len r == n
    array.repeat n (Packed.elem x)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    terminal.print_line (display (Money 1250) [Cents]) t
    terminal.print_line (display (Money 1250) [Whole]) t
    terminal.print_line (display (Money 1250) []) t
    terminal.print_line (display 7 []) t
    let bytes = row 1 3
    terminal.print_line (debug (array.to_list bytes)) t
    terminal.print_line (debug bytes[2]) t
    let strings = row True 2
    terminal.print_line (debug (array.to_list strings)) t
    Success
