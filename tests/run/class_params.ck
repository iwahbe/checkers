module class_params

# Dictionaries of a class of several parameters, for two instances, passed
# through generic code; and a class's type named by both types, laid out
# at run time as each instance's type is.

import std.system (System, ExitCode)
import std.terminal
import std.array

record Format
    prefix~String

record Plain
    sep~String

class Hole s h
    type Cell
    fn hole tag x -> r : tag~s, x~h, r~String
    fn cell tag x -> c : tag~s, x~h, c~Cell

instance Hole Format Int
    type Cell = U8
    fn hole f x
        f.prefix ++ format x
    fn cell f x
        7

instance Hole Plain String
    type Cell = String
    fn hole p x
        x ++ p.sep
    fn cell p x
        x

fn fill_all tag xs -> r : Hole s h, tag~s, xs~List h, r~String
    match xs
        []        -> ""
        x :: rest -> hole tag x ++ fill_all tag rest

fn cells tag x n -> r : Hole s h, tag~s, x~h, n~Nat, r~Array (Hole.Cell s h), len r == n
    array.repeat n (cell tag x)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    terminal.print_line (fill_all (Format "#") [1, 2, 3]) t
    terminal.print_line (fill_all (Plain ";") ["a", "b"]) t
    terminal.print_line (format (array.to_list (cells (Format "") 1 3))) t
    terminal.print_line (format (array.to_list (cells (Plain "") "x" 2))) t
    Success
