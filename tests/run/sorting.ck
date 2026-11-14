# Sorting (D138) and the class `Ord` (D136): lists and arrays, by `Ord`,
# by a key, and by a comparison; a record of the program's own with its own
# instance, and its dictionary passed at run time.
module sorting

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.list (sort, sort_as, sort_by)
import std.array

record Person
    name~String
    age~Nat

# By age, then name: its lemmas use those of `Ord String`.
instance Ord Person
    fn le p q
        p.age < q.age or (p.age == q.age and Ord.le p.name q.name)
    lemma trans p q r
        proof
            if Ord.le p.name q.name and Ord.le q.name r.name
                have Ord.trans p.name q.name r.name
            else
                auto
    lemma total p q
        proof
            have Ord.total p.name q.name
    lemma antisym p q
        proof
            if Ord.le p.name q.name and Ord.le q.name p.name
                have Ord.antisym p.name q.name
            else
                auto

fn show xs term -> r : xs~List a, term~Term, r~Unit
    terminal.print_line (format xs) term

fn names ps -> r : ps~List Person, r~List String
    match ps
        []        -> []
        p :: rest -> p.name :: names rest

# Generic: the dictionary comes from the caller.
fn smallest xs d -> r : Ord a, xs~List a, d~a, r~a
    match sort xs
        []     -> d
        x :: _ -> x

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    let people = [Person "Ada" 36, Person "Bo" 29, Person "Al" 36, Person "Cy" 29]
    show (sort [5, 3, 9, 1, 3]) t
    show (sort ["pear", "apple", "fig", "Banana"]) t
    show (sort [True, False, True]) t
    show (names (sort people)) t
    show (names (sort_as (\p -> p.name) people)) t
    show (names (sort_as (\p -> p.age) people)) t
    show (sort_by (\x y -> x >= y) [5, 3, 9, 1, 3]) t
    show (array.to_list (array.sort (array.from_list [3, 1, 2]))) t
    terminal.print_line (format (array.sort (array.from_list [200, 7, 64]))) t
    terminal.print_line (smallest people (Person "none" 0)).name t
    terminal.print_line (smallest ["b", "a"] "") t
    Success
