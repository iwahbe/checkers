module fix_round_trip

# What a rule made with `fix` reads can be proved: `fix_unfold` unfolds it,
# and an instance's `parse` made with `fix` is the `fix` a lemma names.

import std.parse (Parsable, Token, token, consumed, suffix_trans, fix, fix_unfold)

enum Tok
    Open
    Close
    Leaf

# `Leaf`, or a tree between `Open` and `Close`.
enum Tree
    Tip
    Wrap t : t~Tree

instance Token Tok Tok
    fn token v t
        v

fn tree self top xs -> r : Seq s, Token (Seq.Elem s) Tok,
                           self~(ys~s -> sr~Result (Tree, s) Unit, Seq.size ys < Seq.size top, consumed sr ys),
                           top~ghost s, xs~s, Seq.size xs <= Seq.size top, r~Result (Tree, s) Unit, consumed r xs
    match xs
        x :: rest ->
            match token x Tok
                Leaf  -> Ok (Tip, rest)
                Open  ->
                    match self rest
                        Ok (t, mid) ->
                            match mid
                                y :: after ->
                                    match token y Tok
                                        Close ->
                                            have suffix_trans after mid rest
                                            have suffix_trans after rest xs
                                            Ok (Wrap t, after)
                                        _     -> Err ()
                                []         -> Err ()
                        Err e       -> Err e
                Close -> Err ()
        []        -> Err ()

instance Parsable Tree Tok
    type Error = Unit
    fn parse xs a t
        fix (\zs self -> tree self zs zs) xs

fn toks t tail -> r : t~Tree, tail~List Tok, r~List Tok
    match t
        Tip    -> Leaf :: tail
        Wrap u -> Open :: toks u (Close :: tail)

lemma round t tail : t~Tree, tail~List Tok
    ensures Parsable.parse (toks t tail) Tree Tok == Ok (t, tail)
    proof
        have fix_unfold (\zs self -> tree self zs zs) (toks t tail)
        match t
            Tip    -> auto
            Wrap u -> have round u (Close :: tail)
