module eq_functions

import std.list
import std.terminal (Term)
import std.cown (Cown)
import std.system (System)
import std.decimal (Decimal)
import std.bag (Bag)

# `==` never compares functions, nor capabilities, cowns, futures, files or
# process handles (D125).

fn inc x -> r : x~Nat, r~Nat
    x + 1

record Handler
    name~String
    run~Nat -> Nat

# (a) A function type, or a type containing one: a type error.
fn direct f g : f~(Nat -> Nat), g~(Nat -> Nat)
    f == g

fn in_option f : f~(Nat -> Nat)
    Some f != None

fn in_tuple f : f~(Nat -> Nat)
    (1, f) == (1, inc)

fn in_record h : h~Handler
    h == Handler "inc" inc

check inc == inc

# Allowed: values that contain no function, and specifications, which are
# never compiled.
fn handlers_named a b : a~Handler, b~Handler
    a.name == b.name

fn same_fn f g : f~(Nat -> Nat), g~(Nat -> Nat), f == g
    True

# (b) Through type parameters, directly or through the functions called.
fn same x y : x~a, y~a
    x == y

fn same_twice x y : x~a, y~a
    same x y and same y x

fn same_options x y : x~Option a, y~Option a
    x == y

fn fine n : n~Nat
    same n 1 and same_twice "a" "b" and same_options (Some 1) None

fn generic_fns f : f~(Nat -> Nat)
    same f inc

fn generic_through f : f~(Nat -> Nat)
    same_twice f inc

fn generic_option f : f~(Nat -> Nat)
    same_options (Some f) None

fn from_std f : f~(Nat -> Nat)
    list.contains [inc] f

# An operator section is the same comparison.
fn section f : f~(Nat -> Nat)
    let is_inc = (== inc)
    is_inc f

# (c) Capabilities, cowns, futures, files and process handles, like functions.
fn terms t u : t~Term, u~Term
    t == u

fn cowns c d : c~Cown Nat, d~Cown Nat
    c != d

fn systems s : s~System
    s == s

fn generic_term t : t~Term
    same t t

# Built-in types that do compare.
fn plain a b c : a~Bytes, b~Decimal, c~Bag Int
    a == a and b == b and c == c
