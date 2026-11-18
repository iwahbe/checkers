module smt_well_founded

import std.array

# Types whose values reach the type again only through an array or a
# function. Each has values (an empty array, a function from an empty type),
# and the prover reasons about them.

enum Grid
    Cells cells : cells~Array Grid

enum Empty

enum Absurd
    FromEmpty f : f~(Empty -> Absurd)

record Board
    rows~Array Board

fn width g -> n : g~Grid, n~Nat
    match g
        Cells cells -> len cells

lemma same_grid t u : t~Grid, u~Grid, t == u
    ensures u == t

lemma same_absurd t u : t~Absurd, u~Absurd, t == u
    ensures u == t

lemma rebuilt b : b~Board
    ensures b == Board b.rows

lemma wide g : g~Grid, 0 < width g
    ensures g != Cells (array.from_list [])

lemma first_row b : b~Board, 0 < len b.rows
    ensures b.rows[0] == Board b.rows[0].rows

lemma all_equal t u : t~Grid, u~Grid
    ensures t == u                          # error: two grids can differ

lemma all_differ t u : t~Absurd, u~Absurd
    ensures t != u                          # error: there is one `Absurd`
