module combinators

# Benchmark (§14): a grammar of sums with brackets, `1+(22+333)+4`, read
# from 2 MB of bytes by `std.parse`'s combinators (generic code over
# `Seq`), by the same combinators written for `Bytes` alone, and by a
# reader that reads the grammar by index. `combinators generic`,
# `combinators mono` or `combinators index`; each prints the same.

import std.system (System, ExitCode)
import std.terminal (Term)
import std.string (format)
import std.bytes
import std.parse (consumed, within, suffix_refl, suffix_trans, suffix_size, satisfy, map, many1, chain_left, or_else, fix)

# `n` copies of a term, joined by `+`.
fn input n acc -> r : n~Nat, acc~List Bytes, r~Bytes
    decreasing n
    if n == 0 then bytes.concat (b"0" :: acc) else input (n - 1) (b"+(12+(345+6)+78)+9" :: acc)

# ── Generic: `std.parse` ──

fn digit xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    map (\c -> c - '0') (\ys -> satisfy (\c -> c >= '0' and c <= '9') () ys) xs

fn byte_of c xs -> r : c~Int, xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    satisfy (\k -> k == c) () xs

fn plus xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    byte_of '+' xs

fn number xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    map (\ds -> to_number ds 0) (\ys -> many1 digit ys) xs

fn to_number ds acc -> n : ds~List Int, acc~Int, n~Int
    match ds
        []        -> acc
        d :: rest -> to_number rest (acc * 10 + d)

fn sum xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    fix (\zs self -> chain_left (\ys -> term self zs ys) plus (\a b -> a + b) zs) xs

fn term self top xs -> r : self~(ys~Bytes -> sr~Result (Int, Bytes) Unit, Seq.size ys < Seq.size top, consumed sr ys),
                           top~ghost Bytes, xs~Bytes, Seq.size xs <= Seq.size top, r~Result (Int, Bytes) Unit, consumed r xs
    or_else (\ys -> number ys) (\ys -> bracketed self top ys) xs

fn bracketed self top xs -> r : self~(ys~Bytes -> sr~Result (Int, Bytes) Unit, Seq.size ys < Seq.size top, consumed sr ys),
                                top~ghost Bytes, xs~Bytes, Seq.size xs <= Seq.size top,
                                r~Result (Int, Bytes) Unit, consumed r xs
    match byte_of '(' xs
        Err e         -> Err e
        Ok (_, after) ->
            match self after
                Err e           -> Err e
                Ok (inner, mid) ->
                    match byte_of ')' mid
                        Err e        -> Err e
                        Ok (_, rest) ->
                            have suffix_trans mid after xs
                            have suffix_trans rest mid xs
                            Ok (inner, rest)

fn generic xs -> r : xs~Bytes, r~Int
    match sum xs
        Ok (v, _) -> v
        Err _     -> -1

# ── The same combinators, written for `Bytes` ──

fn b_satisfy f e xs -> r : f~(Int -> Bool), e~err, xs~Bytes, r~Result (Int, Bytes) err, consumed r xs
    match xs
        x :: rest -> if f x then Ok (x, rest) else Err e
        []        -> Err e

fn b_map f p xs -> r : f~(a -> b), p~(ys~Bytes -> pr~Result (a, Bytes) e, len ys <= len xs, consumed pr ys), xs~Bytes,
                       r~Result (b, Bytes) e, consumed r xs
    match p xs
        Ok (v, rest) -> Ok (f v, rest)
        Err x        -> Err x

fn b_or_else p q xs -> r : p~(ys~Bytes -> pr~Result (a, Bytes) e, len ys <= len xs, consumed pr ys),
                           q~(ys~Bytes -> qr~Result (a, Bytes) e, len ys <= len xs, consumed qr ys), xs~Bytes,
                           r~Result (a, Bytes) e, consumed r xs
    match p xs
        Ok v  -> Ok v
        Err _ -> q xs

fn b_many p xs -> r : p~(ys~Bytes -> pr~Result (a, Bytes) e, len ys <= len xs, consumed pr ys), xs~Bytes,
                      r~Result (List a, Bytes) e, within r xs
    decreasing len xs
    match p xs
        Err _       ->
            have suffix_refl xs
            Ok ([], xs)
        Ok (v, mid) ->
            match b_many p mid
                Ok (vs, rest) ->
                    have suffix_trans rest mid xs
                    Ok (v :: vs, rest)
                Err x         -> Err x

fn b_many1 p xs -> r : p~(ys~Bytes -> pr~Result (a, Bytes) e, len ys <= len xs, consumed pr ys), xs~Bytes,
                       r~Result (List a, Bytes) e, consumed r xs
    match p xs
        Err x       -> Err x
        Ok (v, mid) ->
            match b_many p mid
                Ok (vs, rest) ->
                    have suffix_trans rest mid xs
                    have suffix_size rest mid
                    Ok (v :: vs, rest)
                Err x         -> Err x

fn b_chain_left p sep f xs -> r : p~(ys~Bytes -> pr~Result (a, Bytes) e, len ys <= len xs, consumed pr ys),
                                  sep~(ys~Bytes -> qr~Result (b, Bytes) e, len ys < len xs, consumed qr ys),
                                  f~(a -> a -> a), xs~Bytes, r~Result (a, Bytes) e, consumed r xs
    match p xs
        Err x       -> Err x
        Ok (v, mid) ->
            match b_chain_rest p sep f v mid
                Ok (w, rest) ->
                    have suffix_trans rest mid xs
                    have suffix_size rest mid
                    Ok (w, rest)
                Err x        -> Err x

fn b_chain_rest p sep f acc xs -> r : p~(ys~Bytes -> pr~Result (a, Bytes) e, len ys < len xs, consumed pr ys),
                                      sep~(ys~Bytes -> qr~Result (b, Bytes) e, len ys <= len xs, consumed qr ys),
                                      f~(a -> a -> a), acc~a, xs~Bytes, r~Result (a, Bytes) e, within r xs
    decreasing len xs
    match sep xs
        Err _       ->
            have suffix_refl xs
            Ok (acc, xs)
        Ok (_, mid) ->
            match p mid
                Err _         ->
                    have suffix_refl xs
                    Ok (acc, xs)
                Ok (v, after) ->
                    match b_chain_rest p sep f (f acc v) after
                        Ok (w, rest) ->
                            have suffix_trans after mid xs
                            have suffix_trans rest after xs
                            Ok (w, rest)
                        Err x        -> Err x

fn b_fix body xs -> r : xs~Bytes,
                        body~(zs~Bytes -> (self~(ys~Bytes -> sr~Result (a, Bytes) e, len ys < len zs, consumed sr ys)
                                           -> br~Result (a, Bytes) e, consumed br zs)),
                        r~Result (a, Bytes) e, consumed r xs
    decreasing len xs
    body xs (\ys -> b_fix body ys)

fn b_digit xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    b_map (\c -> c - '0') (\ys -> b_satisfy (\c -> c >= '0' and c <= '9') () ys) xs

fn b_byte_of c xs -> r : c~Int, xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    b_satisfy (\k -> k == c) () xs

fn b_plus xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    b_byte_of '+' xs

fn b_number xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    b_map (\ds -> to_number ds 0) (\ys -> b_many1 b_digit ys) xs

fn b_sum xs -> r : xs~Bytes, r~Result (Int, Bytes) Unit, consumed r xs
    b_fix (\zs self -> b_chain_left (\ys -> b_term self zs ys) b_plus (\a b -> a + b) zs) xs

fn b_term self top xs -> r : self~(ys~Bytes -> sr~Result (Int, Bytes) Unit, len ys < len top, consumed sr ys),
                             top~ghost Bytes, xs~Bytes, len xs <= len top, r~Result (Int, Bytes) Unit, consumed r xs
    b_or_else (\ys -> b_number ys) (\ys -> b_bracketed self top ys) xs

fn b_bracketed self top xs -> r : self~(ys~Bytes -> sr~Result (Int, Bytes) Unit, len ys < len top, consumed sr ys),
                                  top~ghost Bytes, xs~Bytes, len xs <= len top,
                                  r~Result (Int, Bytes) Unit, consumed r xs
    match b_byte_of '(' xs
        Err e         -> Err e
        Ok (_, after) ->
            match self after
                Err e           -> Err e
                Ok (inner, mid) ->
                    match b_byte_of ')' mid
                        Err e        -> Err e
                        Ok (_, rest) ->
                            have suffix_trans mid after xs
                            have suffix_trans rest mid xs
                            Ok (inner, rest)

fn mono xs -> r : xs~Bytes, r~Int
    match b_sum xs
        Ok (v, _) -> v
        Err _     -> -1

# ── Hand-written: by index ──

# A value read, and where it ends.
record Read
    value~Int
    stop~Nat

fn digits xs i m -> r : xs~Bytes, i~Nat, i <= len xs, m~Int, r~Read, r.stop <= len xs, r.stop >= i
    decreasing len xs - i
    if i < len xs and xs[i] >= '0' and xs[i] <= '9' then digits xs (i + 1) (m * 10 + (xs[i] - '0')) else Read m i

# A sum from `i`, at most `depth` brackets deep (a bound for termination).
fn mono_sum xs i depth -> r : xs~Bytes, i~Nat, i <= len xs, depth~Nat, r~Read, r.stop <= len xs, r.stop >= i
    decreasing (depth, 2, 0)
    let a = mono_term xs i depth
    mono_rest xs a.stop a.value depth

fn mono_rest xs i acc depth -> r : xs~Bytes, i~Nat, i <= len xs, acc~Int, depth~Nat, r~Read, r.stop <= len xs, r.stop >= i
    decreasing (depth, 1, len xs - i)
    if i < len xs and xs[i] == '+'
        let b = mono_term xs (i + 1) depth
        if b.stop > i + 1 then mono_rest xs b.stop (acc + b.value) depth else Read acc i
    else
        Read acc i

fn mono_term xs i depth -> r : xs~Bytes, i~Nat, i <= len xs, depth~Nat, r~Read, r.stop <= len xs, r.stop >= i
    decreasing (depth, 0, 0)
    if i < len xs and xs[i] == '(' and depth > 0
        let inner = mono_sum xs (i + 1) (depth - 1)
        if inner.stop < len xs and xs[inner.stop] == ')' then Read inner.value (inner.stop + 1) else Read 0 i
    else
        digits xs i 0

fn index xs -> r : xs~Bytes, r~Int
    (mono_sum xs 0 64).value

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let System { term } = sys
    # Unknown when compiling (`none` is 0), so the work is done when the
    # program runs, not when it is compiled (§8.9).
    let none = len args - len args
    let xs = input (none + 120000) []
    let v = match args
        ["mono"]  -> mono xs
        ["index"] -> index xs
        _         -> generic xs
    terminal.print_line format"{v}" term
    Success
