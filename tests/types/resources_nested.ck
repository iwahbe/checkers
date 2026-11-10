# Arguments are evaluated once, before the call: a resource used up inside
# an argument (`size f` in `print_line (format (size f))`) is used once,
# whatever the outer parameter allows. What can be part of the argument's
# value (a closure over it, a partial application, a call that returns it)
# is still used as often as the parameter allows.
module resources_nested

import std.files (File)
import std.terminal (Term)

fn size f -> n : f~File, n~Nat
    files.close f
    0

fn twice g -> r : g~(Unit -> Nat), r~Nat
    g () + g ()

fn keep f -> r : f~File, r~File
    f

fn both f n -> r : f~File, n~Nat, r~Nat
    files.close f
    n

fn twice_on g -> r : g~(Nat -> Nat), r~Nat
    g 1 + g 2

fn same x -> r : x~a, r~a
    x

# Fine: `f` is closed by `size`; `print_line` gets a string.
fn nested f term -> r : f~File, term~Term, r~Unit
    terminal.print_line (format (size f)) term

# Fine: the same, deeper.
fn deeper f term -> r : f~File, term~Term, r~Unit
    terminal.print_line ("size " ++ format (size f + 1)) term

# E0401: the closure may run twice.
fn closure f -> r : f~File, r~Nat
    twice (\u -> size f)

# E0401: `keep f` is the file itself, and `same` may copy it.
fn returned f -> r : f~File, r~File
    same (keep f)

# E0401: `both f` is a function holding the file.
fn partial_app f -> r : f~File, r~Nat
    twice_on (both f)
