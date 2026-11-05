# parallel.ck — parallelism without blocking (SPEC §8.6).
#
#   parallel FILE1 FILE2   reads both files at the same time and reports
#                          whether their contents are identical.

module parallel

import system (System, ExitCode)
import terminal (Term)
import files (Fs, IoError)
import future (Future)
import list (length, take, drop, sorted, perm)

# ── Pure parallelism ─────────────────────────────────────────────────────────
# `par` sorts both halves at once. To the prover `par t == t`, so `sort` is
# still an ordinary pure function and keeps its correctness proof.

export fn sort xs -> out : xs~List Int, out~List Int, sorted out, perm xs out
    decreasing length xs
    match xs
        []  -> []
        [x] -> [x]
        _   ->
            let half = length xs / 2
            let (l, r) = par (sort (take half xs), sort (drop half xs))
            merge l r

fn merge l r -> out : l~List Int, r~List Int, sorted l, sorted r,
                      out~List Int, sorted out, perm (l ++ r) out
    decreasing length l + length r
    match (l, r)
        ([], _) -> r
        (_, []) -> l
        (x :: xs, y :: ys) ->
            if x <= y then x :: merge xs r else y :: merge l ys

# ── Effectful parallelism ────────────────────────────────────────────────────
# Both reads are forked and the join is scheduled straight away; it runs once
# both reads are done. Nothing waits. `main` returns the join's future, and the
# process exits with its value when all work has finished.

export fn main args sys -> code : args~List String, sys~System, code~Future ExitCode
    let System { fs, term, sched } = sys
    match args
        [p1, p2] ->
            a <- fork using sched
                files.read p1 fs
            b <- fork using sched
                files.read p2 fs
            done <- join x = a, y = b using sched
                compare_files p1 x p2 y term
            done
        _ ->
            terminal.eprint_line "usage: parallel FILE1 FILE2" term
            future.ready (Failure 2)

fn compare_files p1 r1 p2 r2 term -> code : p1~String, r1~Result Bytes IoError,
                                            p2~String, r2~Result Bytes IoError,
                                            term~Term, code~ExitCode
    match (r1, r2)
        (Ok x, Ok y) if x == y ->
            terminal.print_line "same" term
            Success
        (Ok _, Ok _) ->
            terminal.print_line "different" term
            Failure 1
        (Err e, _) -> read_failed p1 e term
        (_, Err e) -> read_failed p2 e term

fn read_failed path e term -> code : path~String, e~IoError, term~Term, code~ExitCode
    terminal.eprint_line ("parallel: " ++ path ++ ": " ++ files.describe e) term
    Failure 2

check sort [3, 1, 2] == [1, 2, 3]
check sort [] == []
