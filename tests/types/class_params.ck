module class_params

import std.string (debug)

# A class of several type parameters: which hole types each formatter
# accepts is a property of the pair.

class Display a
    fn display x -> s : x~a, s~String

instance Display Int
    fn display x
        debug x

record Format
    prefix~String

record Page
    title~String

record Plain
    sep~String

class Hole s h
    fn hole tag x -> r : tag~s, x~h, r~String

# Any type with a display.
instance Hole Format a : Display a
    fn hole f x
        f.prefix ++ display x

# Only strings.
instance Hole Page String
    fn hole p x
        p.title ++ x

# Strings and ints, nothing else.
instance Hole Plain String
    fn hole p x
        x

instance Hole Plain Int
    fn hole p x
        debug x ++ p.sep

fn each_used -> r : r~List String
    [hole (Format "f:") 3, hole (Page "p:") "x", hole (Plain ";") "s", hole (Plain ";") 4]

check each_used == ["f:3", "p:x", "s", "4;"]

# A dictionary in scope, from a clause.
fn by_clause t x -> r : Hole s h, t~s, x~h, r~String
    hole t x

check by_clause (Plain ",") 5 == "5,"

# The hole's type isn't known at the use: `Plain` has two instances, so
# the use waits until it is, from the argument.
fn waits -> r : r~String
    (\v -> hole (Plain ";") v) 4

check waits == "4;"

# `Format`'s instance is chosen at once; its `Display a` waits for `a`.
fn context_waits -> r : r~String
    (\v -> hole (Format "f:") v) 2

check context_waits == "f:2"

# A class's type, given by each instance, named with both types.
class Fill s h
    type Options
    fn fill tag x os -> r : tag~s, x~h, os~List Options, r~String

enum Pad
    Left
    Right

instance Fill Format Int
    type Options = Pad
    fn fill f x os
        match os
            [Left] -> " " ++ debug x
            _      -> debug x

fn padded -> r : r~String
    fill (Format "") 7 [Left]

check padded == " 7"

fn options_of xs -> ys : xs~List (Fill.Options Format Int), ys~List Pad
    xs

# In the prover: a known instance's function is visible; a class's lemma
# holds for every dictionary; a class's type at a clause's dictionary is a
# sort of its own.
class Measure a b
    fn measure x y -> n : x~a, y~b, n~Int
    lemma positive x y : x~a, y~b
        ensures measure x y >= 0

instance Measure Bool Int
    fn measure x y
        if x then 1 else 0

fn known -> n : n~Int, n == 1
    measure True 3

fn generic x y -> n : Measure a b, x~a, y~b, n~Int, n >= 0
    have Measure.positive x y
    measure x y + measure x y

fn same_options xs -> ys : Fill s h, xs~List (Fill.Options s h), ys~List (Fill.Options s h), ys == xs
    xs
