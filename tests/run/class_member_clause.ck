module class_member_clause

# A class's function may have a class clause of its own: its field in the
# dictionary takes that dictionary too, passed at each call, so an instance's
# function has the clause like any function with one.

import std.system (System, ExitCode)
import std.terminal
import std.string (debug)

class Weigh w
    fn weigh by xs -> n : Seq s, by~w, xs~s, n~Int

instance Weigh Bool
    fn weigh by xs
        if by then Seq.size xs else 0

instance Weigh Int
    fn weigh by xs
        by * Seq.size xs

fn by_clause xs -> n : Seq s, xs~s, n~Int
    weigh 2 xs

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let term = sys.term
    terminal.print_line (debug (weigh True [1, 2, 3])) term
    terminal.print_line (debug (weigh False [1, 2, 3])) term
    terminal.print_line (debug (weigh 3 "ab")) term
    terminal.print_line (debug (by_clause [True])) term
    Success
