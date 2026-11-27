# compare.ck — our answers against Z3's, query by query.
#
# `main compare [--z3 PROGRAM] [--baseline FILE] [--changed FILE] [--save FILE] DIR`
#
# DIR is a corpus (SPEC §7.2): `MODULE/HASH.smt2` holds a query, and
# `MODULE/HASH.z3` the answer Z3 gave when the corpus was written, after a
# first line `;; work N`. For each query this gives our answer (`reply`),
# timing what `main` does to answer it (reading it and answering it, by
# `std.time`'s monotonic clock), and runs PROGRAM (`z3` by default, looked up on `PATH`) as `PROGRAM -in`,
# with the query on its standard input followed by
# `(get-info :all-statistics)`, for the work and time Z3 used. Then it
# prints the table of rows, our answer against Z3's:
#
#   `Valid` against `sat`      a bug: the command fails
#   `Valid` against `unsat`    agreement
#   `Valid` against `unknown`  we answer where Z3 doesn't
#   `Unknown` against anything a gap, counted by why we gave up
#
# A query holding a `forall` without `:pattern` is a row of its own, with
# Z3's answer, so what answering it `Unknown` costs shows. A query that
# doesn't read is a row of its own too, and so is one Z3 rejects.
#
# Z3 runs as a process here, and in `ckc` it runs in process, through the
# API, so the two can differ: in the work they count, and so, near a work
# limit, in what they answer. Every query whose answer from Z3 now isn't
# the one the corpus records is listed, with both answers, the work each
# used and the query's limit. Nothing is changed to make them agree.
#
# `--save FILE` writes each query's row, one per line: `MODULE/HASH`, a tab,
# the row. `--baseline FILE` reads such a file and prints how many rows
# changed since; `--changed FILE` writes them, one per line: `MODULE/HASH`,
# the row before, the row now, separated by tabs, `-` where there is none.
#
# The repository's baseline is `smt/baseline.tsv`: a change that moves rows
# writes it again with `--save smt/baseline.tsv`, so the rows it moved are
# in its diff. `.github/workflows/compare.yml` runs this on pull requests
# into `smt`.
#
# Exit status: 1 if a row is a bug, 2 if the corpus can't be read or Z3
# can't be run, 0 otherwise.

module compare

import std.system (ExitCode, Success, Failure)
import std.terminal (Term)
import std.files
import std.files (Fs, Entry)
import std.proc
import std.system (Proc, Clock)
import std.time
import std.time (Duration)
import std.string
import std.string (Display, display)
import std.bytes
import std.char
import std.list
import std.parse (Parsable)
import std.decimal
import std.decimal (Decimal, Places)
import smtlib (Query, Opt, Numeral)
import reply (Answer, Valid, Unknown)
import term

let USAGE = "usage: main compare [--z3 PROGRAM] [--baseline FILE] [--changed FILE] [--save FILE] DIR"

# What the command line asks for.
record Options
    z3~String
    baseline~Option String
    changed~Option String
    save~Option String
    dir~Option String

fn options args o -> r : args~List String, o~Options, r~Result Options String
    match args
        "--z3" :: p :: rest       -> options rest (Options p o.baseline o.changed o.save o.dir)
        "--baseline" :: f :: rest -> options rest (Options o.z3 (Some f) o.changed o.save o.dir)
        "--changed" :: f :: rest  -> options rest (Options o.z3 o.baseline (Some f) o.save o.dir)
        "--save" :: f :: rest     -> options rest (Options o.z3 o.baseline o.changed (Some f) o.dir)
        [d]                       ->
            match o.dir
                None   -> Ok (Options o.z3 o.baseline o.changed o.save (Some d))
                Some _ -> Err USAGE
        []                        -> Ok o
        _                         -> Err USAGE

export fn run args io fs p clock -> code : args~List String, io~Term, fs~Fs, p~Proc, clock~Clock, code~ExitCode
    match options args (Options "z3" None None None None)
        Err e -> stop e io
        Ok o  ->
            match o.dir
                None     -> stop USAGE io
                Some dir ->
                    match proc.run o.z3 ["-version"] b"" p
                        Err e   -> stop ("error: can't run " ++ o.z3 ++ ": " ++ files.describe e) io
                        Ok said ->
                            match modules dir fs
                                Err e -> stop ("error: " ++ dir ++ ": " ++ files.describe e) io
                                Ok ms ->
                                    match each_module dir ms o.z3 io fs p clock []
                                        Err e -> stop e io
                                        Ok rs -> report o dir (line_of said.stdout) (corpus_z3 dir fs) (list.reverse rs) io fs

fn stop message io -> code : message~String, io~Term, code~ExitCode
    let _ = terminal.eprint_line message io
    Failure 2

# ── The corpus ───────────────────────────────────────────────────────────────

# The corpus's modules, by name.
fn modules dir fs -> r : dir~String, fs~Fs, r~Result (List String) files.IoError
    match files.list dir fs
        Err e -> Err e
        Ok es -> Ok (list.sort (dirs es))

fn dirs es -> r : es~List Entry, r~List String
    match es
        []        -> []
        e :: rest -> if e.dir then e.name :: dirs rest else dirs rest

# The queries of a module, by hash: the names of its `.smt2` files without
# the extension.
fn hashes es -> r : es~List Entry, r~List String
    match es
        []        -> []
        e :: rest ->
            let b = string.bytes e.name
            if not e.dir and len b > 5 and bytes.matches_at b (len b - 5) b".smt2"
                text (bytes.slice b 0 (len b - 5)) :: hashes rest
            else
                hashes rest

# The Z3 the corpus names, from its `z3-version`.
fn corpus_z3 dir fs -> r : dir~String, fs~Fs, r~Bytes
    match files.read (dir ++ "/z3-version") fs
        Ok b  -> line_of b
        Err _ -> b"(no z3-version)"

fn each_module dir ms z3 io fs p clock acc -> r : dir~String, ms~List String, z3~String, io~Term, fs~Fs, p~Proc,
                                                  clock~Clock,
                                                  acc~List Outcome, r~Result (List Outcome) String
    match ms
        []        -> Ok acc
        m :: rest ->
            match files.list (dir ++ "/" ++ m) fs
                Err e -> Err ("error: " ++ dir ++ "/" ++ m ++ ": " ++ files.describe e)
                Ok es ->
                    let acc2 = try each_query dir m (list.sort (hashes es)) z3 io fs p clock acc
                    each_module dir rest z3 io fs p clock acc2

fn each_query dir m hs z3 io fs p clock acc -> r : dir~String, m~String, hs~List String, z3~String, io~Term,
                                                   fs~Fs, p~Proc, clock~Clock, acc~List Outcome, r~Result (List Outcome) String
    match hs
        []        -> Ok acc
        h :: rest ->
            let base = dir ++ "/" ++ m ++ "/" ++ h
            match (files.read (base ++ ".smt2") fs, files.read (base ++ ".z3") fs)
                (Err e, _)       -> Err ("error: " ++ base ++ ".smt2: " ++ files.describe e)
                (_, Err e)       -> Err ("error: " ++ base ++ ".z3: " ++ files.describe e)
                (Ok src, Ok rec) ->
                    match proc.run z3 ["-in"] (src ++ b"(get-info :all-statistics)\n") p
                        Err e   -> Err ("error: can't run " ++ z3 ++ ": " ++ files.describe e)
                        Ok said ->
                            # What `main` does to answer a query: read it, then answer it.
                            let start = time.now clock
                            let read = smtlib.parse src
                            let ours = match read
                                Err _ -> Unreadable
                                Ok q  ->
                                    let (a, w) = reply.solved q
                                    Answered a w
                            let took = time.since (time.now clock) start
                            let o = outcome (m ++ "/" ++ h) read ours took (recorded rec) (z3_said said.stdout)
                            each_query dir m rest z3 io fs p clock (o :: acc)

# ── Z3's answers ─────────────────────────────────────────────────────────────

# What Z3 said: its output without the statistics, its answer (the output's
# first line, or `rejected` if an error came before it), and the work
# (`:rlimit-count`) and time (`:time`, in hundredths of a second) it used,
# if its statistics say.
record Said
    output~Bytes
    answer~Bytes
    work~Option Nat
    time~Option Nat

fn z3_said out -> r : out~Bytes, r~Said
    match find_last out b"(:" (len out)
        None    -> Said out (answer_of out) None None
        Some at ->
            let stats = bytes.slice out at (len out)
            let body = bytes.slice out 0 at
            Said body (answer_of body) (stat_number stats b":rlimit-count") (stat_time stats)

# The first line of Z3's output, or `rejected` if it is an error: Z3
# carries on after an error, so an answer after one isn't to the query.
fn answer_of out -> r : out~Bytes, r~Bytes
    let first = line_of out
    if bytes.matches_at first 0 b"(error" then b"rejected" else if len first == 0 then b"nothing" else first

# The work recorded in the corpus, and the output.
fn recorded b -> r : b~Bytes, r~Said
    let first = line_of b
    let rest = if len first < len b then bytes.slice b (len first + 1) (len b) else b""
    let work = if bytes.matches_at first 0 b";; work " then natural_at first 8 else None
    Said rest (answer_of rest) work None

fn stat_number stats key -> r : stats~Bytes, key~Bytes, r~Option Nat
    match find stats key 0
        None   -> None
        Some i -> natural_at stats (skip_spaces stats (i + len key))

# `:time S.SS`, in hundredths of a second.
fn stat_time stats -> r : stats~Bytes, r~Option Nat
    match find stats b":time" 0
        None   -> None
        Some i ->
            let j = skip_spaces stats (i + 5)
            match Parsable.parse (bytes.slice stats j (len stats)) Decimal Int
                Err _     -> None
                Ok (d, _) ->
                    let m = decimal.mantissa d
                    let e = decimal.exponent d
                    if m >= 0 and e >= -2 then Some (m * power10 (e + 2)) else None

fn power10 n -> r : n~Nat, r~Nat
    if n == 0 then 1 else 10 * power10 (n - 1)

# ── Rows ─────────────────────────────────────────────────────────────────────

# What we said about a query.
enum Ours
    Answered a work : a~Answer, work~Nat
    Unreadable

# A query's row: our answer, Z3's, and whether the query holds a `forall`
# without `:pattern`.
record Row
    ours~Ours
    z3~Bytes
    unpatterned~Bool

# One query: where it is, its row, the time we took to read and answer it,
# Z3's answer now and the corpus's (`was`), and the query's work limit.
record Outcome
    path~String
    row~Row
    took~Duration
    now~Said
    was~Said
    limit~Option Nat

fn outcome path read ours took was now -> r : path~String, read~Result Query (smtlib.Error src), ours~Ours,
                                              took~Duration, was~Said, now~Said, r~Outcome
    match read
        Err _ -> Outcome path (Row ours now.answer False) took now was None
        Ok q  -> Outcome path (Row ours now.answer (unpatterned q)) took now was (limit q.options)

# Whether the query holds a `forall` without `:pattern`.
fn unpatterned q -> r : q~Query, r~Bool
    no_patterns (term.axioms q.context)

fn no_patterns xs -> r : xs~List term.Axiom, r~Bool
    match xs
        []        -> False
        a :: rest ->
            match a.patterns
                [] -> True
                _  -> no_patterns rest

# `(set-option :reproducible-resource-limit N)`: the work limit `ckc` gives Z3.
fn limit os -> r : os~List Opt, r~Option Nat
    match os
        []        -> None
        o :: rest ->
            match o.value
                Numeral n if o.key == b"reproducible-resource-limit" -> Some n
                _ -> limit rest

# What a row is: `bug`, `agreement`, `ahead` (we answer, Z3 doesn't), `gap`,
# or `no answer from Z3` (it rejected the query, or said nothing).
fn verdict row -> r : row~Row, r~String
    if row.z3 == b"rejected" or row.z3 == b"nothing"
        "no answer from Z3"
    else
        match row.ours
            Unreadable             -> "gap"
            Answered (Unknown _) _ -> "gap"
            Answered Valid _       ->
                if row.z3 == b"sat" then "bug" else if row.z3 == b"unsat" then "agreement" else "ahead"

# A row's name in the files `--save` and `--changed` write: no spaces.
fn key row -> r : row~Row, r~String
    let ours = match row.ours
        Unreadable             -> "unreadable"
        Answered Valid _       -> "valid"
        Answered (Unknown w) _ -> "unknown(" ++ reply.key w ++ ")"
    ours ++ "/" ++ text row.z3 ++ (if row.unpatterned then "/unpatterned" else "")

# A row as the table shows it.
fn ours_text row -> r : row~Row, r~String
    let ours = match row.ours
        Unreadable             -> "doesn't read"
        Answered Valid _       -> "`Valid`"
        Answered (Unknown w) _ -> "`Unknown` (" ++ text (reply.reason w) ++ ")"
    if row.unpatterned then ours ++ ", a `forall` without `:pattern`" else ours

# ── The report ───────────────────────────────────────────────────────────────

# How many queries each row has, by key.
fn tally os acc -> r : os~List Outcome, acc~List (String, (Row, Nat)), r~List (String, (Row, Nat))
    match os
        []        -> acc
        o :: rest -> tally rest (bump (key o.row) o.row acc)

fn bump k row acc -> r : k~String, row~Row, acc~List (String, (Row, Nat)), r~List (String, (Row, Nat))
    match acc
        []                    -> [(k, (row, 1))]
        (k2, (r2, n)) :: rest -> if k2 == k then (k2, (r2, n + 1)) :: rest else (k2, (r2, n)) :: bump k row rest

fn table_lines ts -> r : ts~List (String, (Row, Nat)), r~List String
    match ts
        []                    -> []
        (_, (row, n)) :: rest ->
            ("| " ++ ours_text row ++ " | `" ++ text row.z3 ++ "` | " ++ verdict row ++ " | " ++ display n [] ++ " |")
                :: table_lines rest

fn bugs ts -> r : ts~List (String, (Row, Nat)), r~Nat
    match ts
        []                    -> 0
        (_, (row, n)) :: rest -> (if verdict row == "bug" then n else 0) + bugs rest

fn report o dir z3 corpus os io fs -> code : o~Options, dir~String, z3~Bytes, corpus~Bytes, os~List Outcome,
                                             io~Term, fs~Fs, code~ExitCode
    let ts = list.sort_as first (tally os [])
    let n = list.length os
    let header = ["Compared " ++ display n [] ++ " queries in " ++ dir ++ " with `" ++ o.z3 ++ " -in` (" ++ text z3
                  ++ "; the corpus was written with " ++ text corpus ++ ").", "", "| Ours | Z3's | Verdict | Queries |",
                  "|---|---|---|---|"]
    let b = bugs ts
    let lines = header ++ table_lines ts ++ ["", "Bug rows: " ++ queries b ++ ".", ""] ++ work_lines os ++ [""]
                ++ against_corpus os ++ [""]
    let _ = terminal.print_line (string.concat (between lines)) io
    let current = list.sort_as first (rows_of os)
    let saved = match o.save
        None   -> True
        Some f -> written f (string.concat (join_lines (tab_lines current))) io fs
    let compared = match o.baseline
        None   -> True
        Some f -> against_baseline f o.changed current io fs
    if not saved or not compared then Failure 2 else if b > 0 then Failure 1 else Success

# ── Work and time ────────────────────────────────────────────────────────────

fn work_lines os -> r : os~List Outcome, r~List String
    let (w, missing_w) = sum_work os 0 0
    let (t, missing_t) = sum_time os 0 0
    ["Work: ours " ++ display (sum_ours os 0) [] ++ " (clauses looked at, summed); Z3's " ++ display w [] ++ " (`:rlimit-count`, summed"
     ++ absent missing_w ++ "). The two aren't counted in the same unit.",
     "Time: ours " ++ display (sum_took os (Duration 0)) [] ++ " (reading and answering each query, summed); Z3's "
     ++ display (decimal.scaled t (-2)) [Places 2] ++ " s (its `:time`, summed" ++ absent missing_t ++ ")."]

fn sum_took os acc -> r : os~List Outcome, acc~Duration, r~Duration
    match os
        []        -> acc
        o :: rest -> sum_took rest (acc + o.took)

fn absent n -> r : n~Nat, r~String
    if n == 0 then "" else "; not in the statistics of " ++ queries n

fn sum_ours os acc -> r : os~List Outcome, acc~Nat, r~Nat
    match os
        []        -> acc
        o :: rest ->
            match o.row.ours
                Answered _ w -> sum_ours rest (acc + w)
                Unreadable   -> sum_ours rest acc

fn sum_work os acc missing -> r : os~List Outcome, acc~Nat, missing~Nat, r~(Nat, Nat)
    match os
        []        -> (acc, missing)
        o :: rest ->
            match o.now.work
                Some w -> sum_work rest (acc + w) missing
                None   -> sum_work rest acc (missing + 1)

fn sum_time os acc missing -> r : os~List Outcome, acc~Nat, missing~Nat, r~(Nat, Nat)
    match os
        []        -> (acc, missing)
        o :: rest ->
            match o.now.time
                Some t -> sum_time rest (acc + t) missing
                None   -> sum_time rest acc (missing + 1)

# ── Z3 now against the corpus ────────────────────────────────────────────────

fn against_corpus os -> r : os~List Outcome, r~List String
    let differ = answers_differ os
    let same_answer = count_same_answer os 0
    let same_out = count_same_output os 0
    let same_work = count_same_work os 0
    let n = list.length os
    ["Z3 now against what the corpus records: " ++ display same_answer [] ++ " of "
     ++ queries n ++ " get the same answer, " ++ display same_out [] ++ " the same output (a model may differ), "
     ++ display same_work [] ++ " the same work."]
        ++ (if differ == [] then [] else ["", "Answers that differ:"] ++ differ)

# `n queries`, or `1 query`.
fn queries n -> r : n~Nat, r~String
    display n [] ++ (if n == 1 then " query" else " queries")

fn answers_differ os -> r : os~List Outcome, r~List String
    match os
        []        -> []
        o :: rest ->
            if o.now.answer == o.was.answer
                answers_differ rest
            else
                ("- " ++ o.path ++ ": the corpus records `" ++ text o.was.answer ++ "` (work " ++ work_text o.was.work
                 ++ "), Z3 now answers `" ++ text o.now.answer ++ "` (work " ++ work_text o.now.work ++ ", "
                 ++ time_text o.now.time ++ "); the work limit is " ++ work_text o.limit)
                    :: answers_differ rest

# Hundredths of a second, as seconds: a query stopped by the wall clock
# (its `:timeout`) rather than its work limit shows here.
fn time_text t -> r : t~Option Nat, r~String
    match t
        Some n -> display (decimal.scaled n (-2)) [Places 2] ++ " s"
        None   -> "time not known"

fn work_text w -> r : w~Option Nat, r~String
    match w
        Some n -> display n []
        None   -> "not known"

fn count_same_answer os acc -> r : os~List Outcome, acc~Nat, r~Nat
    match os
        []        -> acc
        o :: rest -> count_same_answer rest (if o.now.answer == o.was.answer then acc + 1 else acc)

fn count_same_output os acc -> r : os~List Outcome, acc~Nat, r~Nat
    match os
        []        -> acc
        o :: rest -> count_same_output rest (if o.now.output == o.was.output then acc + 1 else acc)

fn count_same_work os acc -> r : os~List Outcome, acc~Nat, r~Nat
    match os
        []        -> acc
        o :: rest ->
            let same = match (o.now.work, o.was.work)
                (Some a, Some b) -> a == b
                _                -> False
            count_same_work rest (if same then acc + 1 else acc)

# ── The baseline ─────────────────────────────────────────────────────────────

fn rows_of os -> r : os~List Outcome, r~List (String, String)
    match os
        []        -> []
        o :: rest -> (o.path, key o.row) :: rows_of rest

fn tab_lines rs -> r : rs~List (String, String), r~List String
    match rs
        []             -> []
        (p, k) :: rest -> (p ++ "\t" ++ k) :: tab_lines rest

# The lines with `\n` between them.
fn between ls -> r : ls~List String, r~List String
    match ls
        []        -> []
        [l]       -> [l]
        l :: rest -> l :: "\n" :: between rest

# Each line followed by `\n`.
fn join_lines ls -> r : ls~List String, r~List String
    match ls
        []        -> []
        l :: rest -> l :: "\n" :: join_lines rest

fn written path contents io fs -> ok : path~String, contents~String, io~Term, fs~Fs, ok~Bool
    match files.write path (string.bytes contents) fs
        Ok () -> True
        Err e ->
            let _ = terminal.eprint_line ("error: " ++ path ++ ": " ++ files.describe e) io
            False

# Compare the rows with the baseline in `path`; print how many changed, and
# write them to `changed` if it is given.
fn against_baseline path changed current io fs -> ok : path~String, changed~Option String,
                                                       current~List (String, String), io~Term, fs~Fs, ok~Bool
    match files.read path fs
        Err e ->
            let _ = terminal.eprint_line ("error: " ++ path ++ ": " ++ files.describe e) io
            False
        Ok b  ->
            let before = list.sort_as first (parse_rows (split_lines b 0 0))
            let diffs = changes before current
            let _ = terminal.print_line ("Rows changed since " ++ path ++ ": " ++ display (list.length diffs) [] ++ ".") io
            match changed
                None   -> True
                Some f -> written f (string.concat (join_lines diffs)) io fs

fn parse_rows ls -> r : ls~List Bytes, r~List (String, String)
    match ls
        []        -> []
        l :: rest ->
            match find l b"\t" 0
                None   -> parse_rows rest
                Some i -> (text (bytes.slice l 0 i), text (bytes.slice l (i + 1) (len l))) :: parse_rows rest

# The rows that differ between two lists sorted by path, in the order of
# their paths.
fn changes xs ys -> r : xs~List (String, String), ys~List (String, String), r~List String
    match (xs, ys)
        ([], [])                     -> []
        ((p, a) :: xr, [])           -> (p ++ "\t" ++ a ++ "\t-") :: changes xr []
        ([], (q, b) :: yr)           -> (q ++ "\t-\t" ++ b) :: changes [] yr
        ((p, a) :: xr, (q, b) :: yr) ->
            if p == q
                if a == b then changes xr yr else (p ++ "\t" ++ a ++ "\t" ++ b) :: changes xr yr
            else if p < q
                (p ++ "\t" ++ a ++ "\t-") :: changes xr ys
            else
                (q ++ "\t-\t" ++ b) :: changes xs yr

fn first p -> r : p~(String, b), r~String
    let (k, _) = p
    k

# ── Bytes ────────────────────────────────────────────────────────────────────

# Bytes as text; bytes that aren't UTF-8 are shown as `?`.
fn text b -> r : b~Bytes, r~String
    match string.from_utf8 b
        Some s -> s
        None   -> "?"

# The first line of `b`, without its `\n`.
fn line_of b -> r : b~Bytes, r~Bytes
    bytes.slice b 0 (line_end b 0)

# The offset of the first `\n` at or after `i`, or the end.
fn line_end b i -> j : b~Bytes, i~Nat, i <= len b, j~Nat, i <= j, j <= len b
    decreasing len b - i
    if i < len b and b[i] != '\n' then line_end b (i + 1) else i

# The lines of `b` from `i`, the line being read starting at `start`.
fn split_lines b start i -> r : b~Bytes, start~Nat, i~Nat, start <= i, i <= len b, r~List Bytes
    decreasing len b - i
    if i >= len b
        if start < i then [bytes.slice b start i] else []
    else if b[i] == '\n'
        bytes.slice b start i :: split_lines b (i + 1) (i + 1)
    else
        split_lines b start (i + 1)

# The first offset at or after `i` where `word` is.
fn find b word i -> r : b~Bytes, word~Bytes, i~Nat, i <= len b, r~Option (j~Nat, j + len word <= len b, j < len b)
    decreasing len b - i
    if i >= len b then None else if bytes.matches_at b i word then Some i else find b word (i + 1)

# The last offset before `i` where `word` is.
fn find_last b word i -> r : b~Bytes, word~Bytes, i~Nat, i <= len b, r~Option (j~Nat, j + len word <= len b)
    decreasing i
    if i == 0 then None else if bytes.matches_at b (i - 1) word then Some (i - 1) else find_last b word (i - 1)

fn skip_spaces b i -> j : b~Bytes, i~Nat, i <= len b, j~Nat, j <= len b
    decreasing len b - i
    if i < len b and b[i] == ' ' then skip_spaces b (i + 1) else i

# The number written at `i`, if digits start there.
fn natural_at b i -> r : b~Bytes, i~Nat, i <= len b, r~Option Nat
    if i < len b and char.is_digit b[i]
        let ds = bytes.slice b i (len b)
        have bytes.slice_at b i (len b) 0
        have string.parse_digits ds
        match Parsable.parse ds Int Int
            Ok (n, _) -> Some n
    else
        None
