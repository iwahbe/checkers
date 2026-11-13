# Classes over type constructors (M25, D136): `Functor` at `List`,
# `Option` and `Array`, a program's own instance, and a function generic
# over any `Functor`, its dictionary passed at run time.
module functor

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.array

# A pair of values of one type.
record Two a
    first~a
    second~a

instance Functor Two
    fn fmap g p
        Two (g p.first) (g p.second)

# Generic: works for any `Functor`.
fn doubled xs -> ys : Functor f, xs~f Int, ys~f Int
    fmap (\x -> x * 2) xs

# Generic, and proved for every `Functor` from its lemmas.
lemma doubled_twice xs : Functor f, xs~f Int
    ensures doubled (doubled xs) == fmap (\x -> x * 4) xs
    proof
        have Functor.fmap_comp (\x -> x * 2) (\x -> x * 2) xs

check doubled [1, 2] == [2, 4]
check doubled (Two 3 4) == Two 6 8

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    terminal.print_line (format (doubled [1, 2, 3])) t
    terminal.print_line (format (doubled (Some 5))) t
    terminal.print_line (format (doubled (array.from_list [7, 8]))) t
    let p = doubled (Two 10 20)
    terminal.print_line (format [p.first, p.second]) t
    terminal.print_line (format (fmap (\s -> s ++ "!") ["a", "b"])) t
    Success
