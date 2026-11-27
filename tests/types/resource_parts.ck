# Using part of a value that holds a resource (#647): reading a field or
# indexing uses the whole value, so it may not drop another part that holds
# one (E0406, E0407); a guard can't use an arm's resource (E0408).
module resource_parts

import std.files (File)

record One
    out~File
    lines~Nat

record Two
    a~File
    b~File

fn plain t -> m : t~One, m~Nat
    t.lines

fn one_of_two t : t~Two
    close t.a

fn replaced t f -> r : t~One, f~File, r~One
    One f t.lines

fn indexed a : a~Array File, len a > 0
    close a[0]

# Fine: nothing else holds a resource, and `match` takes a record apart.
fn only t : t~One
    close t.out

fn apart t : t~Two
    match t
        Two a b ->
            close a
            close b

# Specifications read fields freely: they use nothing.
fn counted t -> r : t~One, r~Nat, r == t.lines
    match t
        One out n ->
            close out
            n

# A tuple is taken apart once, whatever its parts.
fn pair p : p~(File, File)
    let (a, b) = p
    close a
    close b

fn half p : p~(File, Nat)
    let (a, _) = p
    close a

# A guard before a resource's arm: when it's false, the next arm has the
# resource, unused.
fn checked f n : f~File, n~Nat
    match f
        g if n > 2 -> close g
        g -> close g

fn ready g -> b : g~File, b~Bool
    close g
    True

fn guarded f : f~File
    match f
        g if ready g -> close g
        g -> close g

# A closure can't capture a resource: it may run any number of times, or
# never.
fn captured f : f~File
    let close_it = \u -> close f
    ()

# One error for reading a field and then using the record.
fn then_whole t -> r : t~One, r~One
    let n = t.lines
    t

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
