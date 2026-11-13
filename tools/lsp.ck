# lsp.ck — `checkers lsp`, the language server (SPEC §15.5, D120). It
# speaks LSP over standard input and output and runs `ckc check --json` on
# every change, with the open documents as an overlay; a newer change of the
# same document kills its check in progress. Diagnostics are published after
# each of the check's phases (types, `check`s, proofs); hover, go to
# definition, references, highlighting and the outline come from the index
# of the document's latest check, waiting for it if needed (D127).

module lsp

import std.system (ExitCode, Proc)
import std.terminal (Term)
import std.files (Fs, File)
import std.proc (Streams, Spawned, Pipe, Discard, Child, Killer)
import std.cown (Cown, Sched)
import std.json (Json, Null, Bool, Num, Str, Arr, Obj)
import std.string
import std.bytes
import std.list
import ck.jsonrpc (Incoming, Message, Malformed, Closed)
import ck.jsonrpc as rpc
import ck.text as tx
import ck.format as formatter

export let VERSION = "0.1.0"

# ── State ────────────────────────────────────────────────────────────────────

# An open document.
record Doc
    uri~String
    path~String
    text~Bytes

# A place in a file: lines from 0, columns in bytes.
record Span
    path~String
    line~Nat
    col~Nat
    end_line~Nat
    end_col~Nat

# A name or token of the index (§15.5): its place, its role, where it is
# defined, what hovering shows ("" for keywords, comments and so on), and the
# description of what it refers to ("" when there is none, D128).
record Entry
    at~Span
    role~String
    def~Option Span
    hover~String
    doc~String

# A diagnostic as the compiler gave it, with its phase.
record Diag
    at~Span
    phase~String
    json~Json

# What the checks share: each root's latest check and diagnostics (a check's
# proof diagnostics stay until its root's next check gets that far, so they
# don't flicker), the index of each file, and the requests waiting for one.
record Shared
    roots~List Root
    index~List Entry
    pending~List Pending

# One checked file (a root): its latest check (only its results are shown),
# whether the index has the file as that check saw it, the diagnostics
# showing, and its last proof diagnostics. A file's diagnostics are those
# every root has for it (a module two open files import is checked with each).
record Root
    path~String
    gen~Nat
    indexed~Bool
    showing~List Diag
    proofs~List Diag

# A request about a file waiting for its index: its answer is `f` of it.
record Pending
    id~Json
    path~String
    f~(List Entry -> Json)

# The main loop's state: the open documents, the last check's number, and
# a way to end each document's check in progress.
record Server
    docs~List Doc
    gen~Nat
    killers~List (String, Killer)
    shutdown~Bool

# A check in progress: the compiler's output and the child.
enum Job
    Running out child acc : out~File, child~Child, acc~Acc
    Finished

# What doesn't change once the client is initialized: the system's
# capabilities, the shared cowns, the compiler and its package flags, and
# whether positions are in UTF-8 (else UTF-16).
record Caps
    fs~Fs
    proc~Proc
    sched~Sched
    out~Cown File
    shared~Cown Shared
    ckc~String
    flags~List String
    utf8~Bool

# ── Documents ────────────────────────────────────────────────────────────────

partial fn doc_of uri docs -> r : uri~String, docs~List Doc, r~Option Doc
    match docs
        []        -> None
        d :: rest -> if d.uri == uri then Some d else doc_of uri rest

partial fn doc_at path docs -> r : path~String, docs~List Doc, r~Option Doc
    match docs
        []        -> None
        d :: rest -> if d.path == path then Some d else doc_at path rest

partial fn without uri docs -> r : uri~String, docs~List Doc, r~List Doc
    match docs
        []        -> []
        d :: rest -> if d.uri == uri then without uri rest else d :: without uri rest

# The text of a file: the open document's, else the file's on disk.
partial fn text_of path docs fs -> r : path~String, docs~List Doc, fs~Fs, r~Bytes
    match doc_at path docs
        Some d -> d.text
        None   ->
            match files.read path fs
                Ok b  -> b
                Err _ -> b""

# ── Positions ────────────────────────────────────────────────────────────────

# An LSP position for a line and byte column of `text`.
partial fn position text line col utf8 -> j : text~Bytes, line~Nat, col~Nat, utf8~Bool, j~Json
    let c = if utf8 then col else tx.utf16_of (tx.line_at text line) col
    rpc.obj [("line", rpc.num line), ("character", rpc.num c)]

partial fn range_of text s utf8 -> j : text~Bytes, s~Span, utf8~Bool, j~Json
    rpc.obj [("start", position text s.line s.col utf8), ("end", position text s.end_line s.end_col utf8)]

partial fn location s docs fs utf8 -> j : s~Span, docs~List Doc, fs~Fs, utf8~Bool, j~Json
    let t = if utf8 then b"" else text_of s.path docs fs
    rpc.obj [("uri", Str (tx.uri_of s.path)), ("range", range_of t s utf8)]

# The byte column of a request's position.
partial fn byte_col text line ch utf8 -> c : text~Bytes, line~Nat, ch~Nat, utf8~Bool, c~Nat
    if utf8 then ch else tx.byte_of (tx.line_at text line) ch

# ── The compiler's output ────────────────────────────────────────────────────

partial fn pair_at key j -> r : key~String, j~Json, r~Option (Nat, Nat)
    match rpc.get key j
        Some (Arr [l, c]) ->
            match (rpc.nat_of l, rpc.nat_of c)
                (Some a, Some b) -> Some (a, b)
                _                -> None
        _                 -> None

partial fn span_of j -> r : j~Json, r~Option Span
    match (rpc.str_at ["path"] j, pair_at "start" j, pair_at "end" j)
        (Some p, Some (l, c), Some (el, ec)) -> Some (Span p l c el ec)
        _                                    -> None

partial fn str_or key j -> s : key~String, j~Json, s~String
    match rpc.str_at [key] j
        Some s -> s
        None   -> ""

# A compiler diagnostic as an LSP one, without its range (set when published).
partial fn diagnostic j -> d : j~Json, d~Json
    let sev = if str_or "severity" j == "error" then 1 else 2
    let label = str_or "label" j
    let notes = match rpc.get "notes" j
        Some (Arr ns) -> note_lines ns
        _             -> ""
    let help = str_or "help" j
    let more = (if label == "" then "" else "\n" ++ label) ++ notes ++ (if help == "" then "" else "\nhelp: " ++ help)
    rpc.obj [
        ("severity", rpc.num sev), ("code", Str (str_or "code" j)), ("source", Str "checkers"),
        ("message", Str (str_or "message" j ++ more))]

partial fn note_lines ns -> s : ns~List Json, s~String
    match ns
        []            -> ""
        Str n :: rest -> "\nnote: " ++ n ++ note_lines rest
        _ :: rest     -> note_lines rest

# What a check has read so far, and how many phases it finished.
record Acc
    diags~List Diag
    index~List Entry
    phases~Nat

# Read the compiler's lines until it ends, publishing after each phase.
# Read the compiler's lines up to the end of a phase, or to its end.
partial fn pump out acc g docs c -> r : out~File, acc~Acc, g~Nat, docs~List Doc, c~Caps, r~(Acc, File)
    line <- files.read_line out
    match line
        None   -> (acc, out)
        Some l ->
            match json.parse (string.bytes l)
                Err _ -> pump out acc g docs c
                Ok j  ->
                    let kind = str_or "kind" j
                    if kind == "done"
                        # Stop here: the phase is published by `step`.
                        (Acc acc.diags acc.index (acc.phases + 1), out)
                    else if kind == "diagnostic"
                        match span_of j
                            Some s ->
                                let d = Diag s (str_or "phase" j) (diagnostic j)
                                pump out (Acc (d :: acc.diags) acc.index acc.phases) g docs c
                            None   -> pump out acc g docs c
                    else if kind == "name" or kind == "token"
                        match span_of j
                            Some s ->
                                let def = match rpc.get "def" j
                                    Some d -> span_of d
                                    None   -> None
                                let e = Entry s (str_or "class" j) def (str_or "hover" j) (str_or "doc" j)
                                pump out (Acc acc.diags (e :: acc.index) acc.phases) g docs c
                            None   -> pump out acc g docs c
                    else
                        pump out acc g docs c

partial fn not_proof ds -> r : ds~List Diag, r~List Diag
    match ds
        []        -> []
        d :: rest -> if d.phase == "proofs" then not_proof rest else d :: not_proof rest

partial fn paths_of ds acc -> r : ds~List Diag, acc~List String, r~List String
    match ds
        []        -> acc
        d :: rest -> paths_of rest (if list.contains acc d.at.path then acc else d.at.path :: acc)

partial fn of_path path ds -> r : path~String, ds~List Diag, r~List Diag
    match ds
        []        -> []
        d :: rest -> if d.at.path == path then d :: of_path path rest else of_path path rest

# After a phase of check `g` of `root`, if it is still the root's latest:
# publish the diagnostics, or take the index and answer the requests
# waiting for it.
partial fn publish phase acc g root docs c : phase~String, acc~Acc, g~Nat, root~String, docs~List Doc, c~Caps
    let sched = c.sched
    when sh = c.shared, o = c.out using sched
        let before = root_in root sh.roots
        if before.gen != g
            (sh, o)
        else if phase == "index"
            # It covers the root's file only.
            let index = acc.index ++ not_in root sh.index
            let roots = Root root g True before.showing before.proofs :: other_roots root sh.roots
            _ <- answer_all (of_root root sh.pending) index o
            (Shared roots index (not_of_root root sh.pending), o)
        else
            # Until this check's proofs are known, its root's last ones stay.
            let proofs = if phase == "proofs" then of_phase "proofs" acc.diags else before.proofs
            let showing = not_proof acc.diags ++ proofs
            let roots = Root root g before.indexed showing proofs :: other_roots root sh.roots
            let touched = paths_of showing (paths_of before.showing [])
            _ <- send_all touched (all_showing roots) docs c o
            (Shared roots sh.index sh.pending, o)
    ()

# A check `g` of `root` ended without its index (the compiler failed): if it
# is the root's latest, answer the requests waiting for it with what there is.
partial fn settle g root c : g~Nat, root~String, c~Caps
    let sched = c.sched
    when sh = c.shared, o = c.out using sched
        let before = root_in root sh.roots
        if before.gen != g or before.indexed
            (sh, o)
        else
            let roots = Root root g True before.showing before.proofs :: other_roots root sh.roots
            _ <- answer_all (of_root root sh.pending) sh.index o
            (Shared roots sh.index (not_of_root root sh.pending), o)
    ()

partial fn answer_all ps index o -> r : ps~List Pending, index~List Entry, o~File, r~((), File)
    match ps
        []        -> ((), o)
        p :: rest ->
            _ <- rpc.write (rpc.response p.id (p.f index)) o
            answer_all rest index o

# The requests about `path`, oldest first.
partial fn of_root path ps -> r : path~String, ps~List Pending, r~List Pending
    match ps
        []        -> []
        p :: rest -> if p.path == path then of_root path rest ++ [p] else of_root path rest

partial fn not_of_root path ps -> r : path~String, ps~List Pending, r~List Pending
    match ps
        []        -> []
        p :: rest -> if p.path == path then not_of_root path rest else p :: not_of_root path rest

# A file never checked counts as indexed: there is nothing to wait for.
partial fn root_in path roots -> r : path~String, roots~List Root, r~Root
    match roots
        []        -> Root path 0 True [] []
        x :: rest -> if x.path == path then x else root_in path rest

partial fn other_roots path roots -> r : path~String, roots~List Root, r~List Root
    match roots
        []        -> []
        x :: rest -> if x.path == path then other_roots path rest else x :: other_roots path rest

# Every root's diagnostics, each once.
partial fn all_showing roots -> r : roots~List Root, r~List Diag
    match roots
        []        -> []
        x :: rest -> add_new x.showing (all_showing rest)

partial fn add_new ds acc -> r : ds~List Diag, acc~List Diag, r~List Diag
    match ds
        []        -> acc
        d :: rest -> add_new rest (if has_diag d acc then acc else d :: acc)

partial fn has_diag d ds -> r : d~Diag, ds~List Diag, r~Bool
    match ds
        []        -> False
        e :: rest -> (e.at == d.at and e.json == d.json) or has_diag d rest

partial fn not_in path es -> r : path~String, es~List Entry, r~List Entry
    match es
        []        -> []
        e :: rest -> if e.at.path == path then not_in path rest else e :: not_in path rest

partial fn of_phase phase ds -> r : phase~String, ds~List Diag, r~List Diag
    match ds
        []        -> []
        d :: rest -> if d.phase == phase then d :: of_phase phase rest else of_phase phase rest

# `publishDiagnostics` for each path.
partial fn send_all paths ds docs c o -> r : paths~List String, ds~List Diag, docs~List Doc, c~Caps, o~File,
                                             r~((), File)
    match paths
        []        -> ((), o)
        p :: rest ->
            let t = if c.utf8 then b"" else text_of p docs c.fs
            let items = list.map (\d -> with_range t d c.utf8) (of_path p ds)
            let params = rpc.obj [("uri", Str (tx.uri_of p)), ("diagnostics", Arr items)]
            _ <- rpc.write (rpc.notification "textDocument/publishDiagnostics" params) o
            send_all rest ds docs c o

partial fn with_range t d utf8 -> j : t~Bytes, d~Diag, utf8~Bool, j~Json
    match d.json
        Obj fields -> rpc.obj (("range", range_of t d.at utf8) :: fields)
        other      -> other

# ── Checks ───────────────────────────────────────────────────────────────────

# The overlay: each open document's text, by path.
partial fn overlay docs -> j : docs~List Doc, j~Json
    rpc.obj (list.map (\d -> (d.path, Str (as_string d.text))) docs)

fn as_string b -> s : b~Bytes, s~String
    match string.from_utf8 b
        Some s -> s
        None   -> ""

partial fn feed input o -> r : input~Bytes, o~File, r~()
    _ <- files.write_bytes input o
    files.close o

# Start a check of `doc`, killing its check in progress (D127 e).
partial fn start doc st c -> r : doc~Doc, st~Server, c~Caps, r~Server
    match killer_of doc.path st.killers
        Some k -> proc.kill k
        None   -> ()
    let others = other_killers doc.path st.killers
    let g = st.gen + 1
    let sched = c.sched
    let path = doc.path
    when sh = c.shared using sched
        let before = root_in path sh.roots
        let roots = Root path g False before.showing before.proofs :: other_roots path sh.roots
        Shared roots sh.index sh.pending
    let args = c.flags ++ ["check", "--json", "--overlay", "-", doc.path]
    let docs = st.docs
    match proc.spawn c.ckc args (Streams Pipe Pipe Discard) c.proc
        Err e                           ->
            show_error ("could not run `" ++ c.ckc ++ "`: " ++ files.describe e ++ "; set CKC to the compiler") c
            settle g doc.path c
            Server st.docs g others st.shutdown
        Ok (Spawned child input out ()) ->
            feed (string.bytes (json.render (overlay st.docs))) input
            let (child, k) = proc.killer child
            let job = cown.new (Running out child (Acc [] [] 0)) c.sched
            step job g doc.path docs c
            Server st.docs g ((doc.path, k) :: others) st.shutdown

partial fn killer_of path ks -> r : path~String, ks~List (String, Killer), r~Option Killer
    match ks
        []             -> None
        (p, k) :: rest -> if p == path then Some k else killer_of path rest

partial fn other_killers path ks -> r : path~String, ks~List (String, Killer), r~List (String, Killer)
    match ks
        []             -> []
        (p, k) :: rest -> if p == path then other_killers path rest else (p, k) :: other_killers path rest

partial fn kill_all ks : ks~List (String, Killer)
    match ks
        []             -> ()
        (_, k) :: rest ->
            proc.kill k
            kill_all rest

# One phase of a check: read it, publish it, and go on in a new behaviour, so
# the publication (on other cowns) needn't wait for the rest of the output.
partial fn step job g root docs c : job~Cown Job, g~Nat, root~String, docs~List Doc, c~Caps
    let sched = c.sched
    when j = job using sched
        match j
            Running o ch acc ->
                let (acc2, o2) = pump o acc g docs c
                if acc2.phases > acc.phases
                    publish (phase_name acc2.phases) acc2 g root docs c
                    step job g root docs c
                    Running o2 ch acc2
                else
                    files.close o2
                    let code = proc.wait ch
                    # 137: killed by a newer check.
                    match code
                        Ok n if acc2.phases == 0 and n != 137 ->
                            show_error ("`" ++ c.ckc ++ "` stopped without checking (exit " ++ format n ++ ")") c
                        _ -> ()
                    if acc2.phases < 2 then settle g root c else ()
                    Finished
            Finished         -> Finished
    ()

fn phase_name n -> s : n~Nat, s~String
    if n == 1 then "types" else if n == 2 then "index" else if n == 3 then "checks" else "proofs"

# ── Requests ─────────────────────────────────────────────────────────────────

fn contains_pos e line col : e~Entry, line~Nat, col~Nat
    e.at.line == line and e.at.end_line == line and e.at.col <= col and col < e.at.end_col

# The name at a position of a file.
partial fn name_at path line col es -> r : path~String, line~Nat, col~Nat, es~List Entry, r~Option Entry
    match es
        []        -> None
        e :: rest ->
            if e.at.path == path and e.hover != "" and contains_pos e line col
                Some e
            else
                name_at path line col rest

# The document and byte position a request is about.
record Where
    doc~Doc
    line~Nat
    col~Nat

partial fn where_of params docs utf8 -> r : params~Json, docs~List Doc, utf8~Bool, r~Option Where
    match (rpc.str_at ["textDocument", "uri"] params, rpc.nat_at ["position", "line"] params,
           rpc.nat_at ["position", "character"] params)
        (Some uri, Some line, Some ch) ->
            match doc_of uri docs
                Some d -> Some (Where d line (byte_col d.text line ch utf8))
                None   -> None
        _                              -> None

partial fn hover w es c -> j : w~Where, es~List Entry, c~Caps, j~Json
    match name_at w.doc.path w.line w.col es
        None   -> Null
        Some e ->
            let doc = if e.doc == "" then "" else "\n\n" ++ e.doc
            let md = rpc.obj [("kind", Str "markdown"), ("value", Str ("```checkers\n" ++ e.hover ++ "\n```" ++ doc))]
            rpc.obj [("contents", md), ("range", range_of w.doc.text e.at c.utf8)]

partial fn definition w es docs c -> j : w~Where, es~List Entry, docs~List Doc, c~Caps, j~Json
    match name_at w.doc.path w.line w.col es
        Some e ->
            match e.def
                Some s -> location s docs c.fs c.utf8
                None   -> Null
        None   -> Null

# Reply to request `id`, about the file at `path`, with `f` of the index,
# from a behaviour on the shared cown (which holds the index) and the
# output: at once if the index has the file's latest check, else when it
# does (D127 c).
partial fn answer id path f c : id~Json, path~String, f~(List Entry -> Json), c~Caps
    let sched = c.sched
    when sh = c.shared, o = c.out using sched
        if (root_in path sh.roots).indexed
            _ <- rpc.write (rpc.response id (f sh.index)) o
            (sh, o)
        else
            (Shared sh.roots sh.index (Pending id path f :: sh.pending), o)
    ()

# Tell the user something went wrong (`window/showMessage`).
partial fn show_error message c : message~String, c~Caps
    let params = rpc.obj [("type", rpc.num 1), ("message", Str ("checkers: " ++ message))]
    reply (rpc.notification "window/showMessage" params) c

# The uses of the name under the cursor in the open files' indexes, and its
# definition if `declaration` (D127 f).
partial fn references w es declaration docs c -> j : w~Where, es~List Entry, declaration~Bool, docs~List Doc,
                                                     c~Caps, j~Json
    match name_at w.doc.path w.line w.col es
        Some e ->
            match e.def
                Some d ->
                    let uses = uses_of d (sort es) []
                    let all = if declaration then d :: uses else uses
                    Arr (list.map (\s -> location s docs c.fs c.utf8) all)
                None   -> Arr []
        None   -> Null

# The places of the names defined at `d` (but `d`), each once.
partial fn uses_of d es acc -> r : d~Span, es~List Entry, acc~List Span, r~List Span
    match es
        []        -> list.reverse acc
        e :: rest ->
            let new = e.def == Some d and e.at != d and not (list.contains acc e.at)
            uses_of d rest (if new then e.at :: acc else acc)

# Reply with a value that needs no index, in order with the other replies.
partial fn reply msg c : msg~Json, c~Caps
    let sched = c.sched
    when o = c.out using sched
        _ <- rpc.write msg o
        o
    ()

# The semantic token types and modifiers (`initialize`'s legend).
let TOKEN_TYPES = ["namespace", "type", "enumMember", "property", "function", "parameter", "variable",
                   "keyword", "comment", "string", "number"]
let TOKEN_MODIFIERS = ["declaration", "readonly"]

fn type_index role -> n : role~String, n~Nat
    position_in role ["module", "type", "constructor", "field", "function", "parameter", "variable", "keyword",
                      "comment", "string", "number", "lemma", "constant"] 0

# Lemmas are shown as functions, constants as (read-only) variables.
fn position_in role names k -> n : role~String, names~List String, k~Nat, n~Nat
    match names
        []        -> 10
        x :: rest ->
            if x == role
                if k == 11 then 4 else if k == 12 then 6 else k
            else
                position_in role rest (k + 1)

fn is_declaration e : e~Entry
    match e.def
        Some d -> d.path == e.at.path and d.line == e.at.line and d.col == e.at.col
        None   -> False

fn modifiers e -> n : e~Entry, n~Nat
    (if is_declaration e then 1 else 0) + (if e.role == "constant" then 2 else 0)

fn before a b : a~Entry, b~Entry
    a.at.line < b.at.line or (a.at.line == b.at.line and a.at.col < b.at.col)

partial fn merge xs ys -> r : xs~List Entry, ys~List Entry, r~List Entry
    match (xs, ys)
        ([], _)            -> ys
        (_, [])            -> xs
        (x :: xr, y :: yr) -> if before y x then y :: merge xs yr else x :: merge xr ys

partial fn halves xs l r -> out : xs~List Entry, l~List Entry, r~List Entry, out~(List Entry, List Entry)
    match xs
        []             -> (l, r)
        [x]            -> (x :: l, r)
        x :: y :: rest -> halves rest (x :: l) (y :: r)

partial fn sort xs -> r : xs~List Entry, r~List Entry
    match xs
        []  -> []
        [x] -> [x]
        _   ->
            let (a, b) = halves xs [] []
            merge (sort a) (sort b)

partial fn in_file path es -> r : path~String, es~List Entry, r~List Entry
    match es
        []        -> []
        e :: rest -> if e.at.path == path and e.at.line == e.at.end_line then e :: in_file path rest else in_file path rest

# Drop entries at the same place as the one before (a name met twice).
partial fn distinct es prev -> r : es~List Entry, prev~Option Entry, r~List Entry
    match es
        []        -> []
        e :: rest ->
            match prev
                Some p if p.at.line == e.at.line and p.at.col == e.at.col -> distinct rest prev
                _ -> e :: distinct rest (Some e)

# The encoded tokens: five numbers each, relative to the one before.
partial fn encode es text utf8 pl pc -> r : es~List Entry, text~Bytes, utf8~Bool, pl~Nat, pc~Nat, r~List Json
    match es
        []        -> []
        e :: rest ->
            let line = if utf8 then b"" else tx.line_at text e.at.line
            let col = if utf8 then e.at.col else tx.utf16_of line e.at.col
            let stop = if utf8 then e.at.end_col else tx.utf16_of line e.at.end_col
            let dl = if e.at.line >= pl then e.at.line - pl else 0
            let dc = if dl == 0 and col >= pc then col - pc else col
            let n = if stop >= col then stop - col else 0
            rpc.num dl :: rpc.num dc :: rpc.num n :: rpc.num (type_index e.role) :: rpc.num (modifiers e)
                :: encode rest text utf8 e.at.line col

partial fn semantic_tokens doc es c -> j : doc~Doc, es~List Entry, c~Caps, j~Json
    let mine = distinct (sort (in_file doc.path es)) None
    rpc.obj [("data", Arr (encode mine doc.text c.utf8 0 0))]

# The outline: the file's declarations.
fn symbol_kind role -> n : role~String, n~Nat
    if role == "type"
        23
    else if role == "constructor"
        22
    else if role == "constant"
        14
    else if role == "field"
        8
    else
        12

fn outlined e : e~Entry
    is_declaration e and (e.role == "function" or e.role == "lemma" or e.role == "type"
                          or e.role == "constructor" or e.role == "constant" or e.role == "field")

partial fn name_text text s -> r : text~Bytes, s~Span, r~String
    let line = tx.line_at text s.line
    if s.col <= s.end_col and s.end_col <= len line
        as_string (bytes.slice line s.col s.end_col)
    else
        ""

partial fn symbols doc es c -> j : doc~Doc, es~List Entry, c~Caps, j~Json
    let mine = distinct (sort (in_file doc.path es)) None
    Arr (symbol_list mine doc c)

partial fn symbol_list es doc c -> r : es~List Entry, doc~Doc, c~Caps, r~List Json
    match es
        []        -> []
        e :: rest ->
            if outlined e
                let loc = rpc.obj [("uri", Str doc.uri), ("range", range_of doc.text e.at c.utf8)]
                let s = rpc.obj [("name", Str (name_text doc.text e.at)), ("kind", rpc.num (symbol_kind e.role)),
                                 ("location", loc)]
                s :: symbol_list rest doc c
            else
                symbol_list rest doc c

# The whole document, formatted: one edit, or none.
partial fn formatting doc c -> j : doc~Doc, c~Caps, j~Json
    match formatter.format doc.text
        Err _  -> Arr []
        Ok out ->
            if out == doc.text
                Arr []
            else
                let lines = tx.line_count doc.text
                let whole = rpc.obj [
                    ("start", rpc.obj [("line", rpc.num 0), ("character", rpc.num 0)]),
                    ("end", rpc.obj [("line", rpc.num (lines + 1)), ("character", rpc.num 0)])]
                Arr [rpc.obj [("range", whole), ("newText", Str (as_string out))]]

# ── The main loop ────────────────────────────────────────────────────────────

partial fn strings xs -> r : xs~List String, r~List Json
    list.map (\x -> Str x) xs

partial fn capabilities utf8 -> j : utf8~Bool, j~Json
    let legend = rpc.obj [("tokenTypes", Arr (strings TOKEN_TYPES)), ("tokenModifiers", Arr (strings TOKEN_MODIFIERS))]
    let caps = rpc.obj [
        ("positionEncoding", Str (if utf8 then "utf-8" else "utf-16")),
        ("textDocumentSync", rpc.obj [("openClose", Bool True), ("change", rpc.num 1)]),
        ("hoverProvider", Bool True),
        ("definitionProvider", Bool True),
        ("referencesProvider", Bool True),
        ("documentFormattingProvider", Bool True),
        ("documentSymbolProvider", Bool True),
        ("semanticTokensProvider", rpc.obj [("legend", legend), ("full", Bool True)])]
    rpc.obj [("capabilities", caps), ("serverInfo", rpc.obj [("name", Str "checkers"), ("version", Str VERSION)])]

# Whether the client offers UTF-8 positions.
partial fn offers_utf8 params -> r : params~Json, r~Bool
    match rpc.at ["capabilities", "general", "positionEncodings"] params
        Some (Arr es) -> list.contains es (Str "utf-8")
        _             -> False

partial fn opened params -> r : params~Json, r~Option Doc
    match (rpc.str_at ["textDocument", "uri"] params, rpc.str_at ["textDocument", "text"] params)
        (Some uri, Some t) ->
            match tx.path_of uri
                Some p -> Some (Doc uri p (string.bytes t))
                None   -> None
        _                  -> None

# The text of the last full-text change.
partial fn changed params -> r : params~Json, r~Option Doc
    match (rpc.str_at ["textDocument", "uri"] params, rpc.get "contentChanges" params)
        (Some uri, Some (Arr cs)) ->
            match (tx.path_of uri, last_text cs None)
                (Some p, Some t) -> Some (Doc uri p (string.bytes t))
                _                -> None
        _                         -> None

partial fn last_text cs found -> r : cs~List Json, found~Option String, r~Option String
    match cs
        []        -> found
        c :: rest ->
            match rpc.str_at ["text"] c
                Some t -> last_text rest (Some t)
                None   -> last_text rest found

# Handle one message; `None` when the server should stop, with its exit code.
partial fn handle m st c -> r : m~Json, st~Server, c~Caps, r~(Server, Option ExitCode)
    let method = match rpc.str_at ["method"] m
        Some x -> x
        None   -> ""
    let id = rpc.get "id" m
    let params = match rpc.get "params" m
        Some p -> p
        None   -> Null
    let docs = st.docs
    let keep = (st, None)
    if method == "exit"
        (st, Some (if st.shutdown then Success else Failure 1))
    else if method == "shutdown"
        kill_all st.killers
        match id
            Some i -> reply (rpc.response i Null) c
            None   -> ()
        (Server st.docs st.gen [] True, None)
    else if method == "textDocument/didOpen" or method == "textDocument/didChange"
        let d = if method == "textDocument/didOpen" then opened params else changed params
        match d
            Some doc ->
                let st2 = Server (doc :: without doc.uri st.docs) st.gen st.killers st.shutdown
                (start doc st2 c, None)
            None     -> keep
    else if method == "textDocument/didClose"
        match rpc.str_at ["textDocument", "uri"] params
            Some uri -> (Server (without uri st.docs) st.gen st.killers st.shutdown, None)
            None     -> keep
    else
        match id
            None   -> keep
            Some i ->
                let utf8 = c.utf8
                if method == "textDocument/hover" or method == "textDocument/definition"
                    or method == "textDocument/references"
                    match where_of params docs utf8
                        Some w ->
                            let path = w.doc.path
                            if method == "textDocument/hover"
                                answer i path (\es -> hover w es c) c
                            else if method == "textDocument/definition"
                                answer i path (\es -> definition w es docs c) c
                            else
                                let decl = rpc.at ["context", "includeDeclaration"] params == Some (Bool True)
                                answer i path (\es -> references w es decl docs c) c
                        None   -> reply (rpc.response i Null) c
                    keep
                else if method == "textDocument/semanticTokens/full" or method == "textDocument/documentSymbol"
                    or method == "textDocument/formatting"
                    match rpc.str_at ["textDocument", "uri"] params
                        Some uri ->
                            match doc_of uri docs
                                Some doc ->
                                    if method == "textDocument/semanticTokens/full"
                                        answer i doc.path (\es -> semantic_tokens doc es c) c
                                    else if method == "textDocument/documentSymbol"
                                        answer i doc.path (\es -> symbols doc es c) c
                                    else
                                        reply (rpc.response i (formatting doc c)) c
                                None     -> reply (rpc.response i Null) c
                        None     -> reply (rpc.response i Null) c
                    keep
                else
                    reply (rpc.error_response i (0 - 32601) ("unknown method `" ++ method ++ "`")) c
                    keep

partial fn serve input st c -> r : input~File, st~Server, c~Caps, r~(ExitCode, File)
    m <- rpc.read input
    match m
        Closed      -> (Failure 1, input)
        Malformed _ -> serve input st c
        Message msg ->
            let (st2, stop) = handle msg st c
            match stop
                Some code -> (code, input)
                None      -> serve input st2 c

# Wait for `initialize`, answer it, then serve.
partial fn begin input c -> r : input~File, c~Caps, r~(ExitCode, File)
    m <- rpc.read input
    match m
        Closed      -> (Failure 1, input)
        Malformed _ -> begin input c
        Message msg ->
            match (rpc.str_at ["method"] msg, rpc.get "id" msg)
                (Some "initialize", Some id) ->
                    let params = match rpc.get "params" msg
                        Some p -> p
                        None   -> Null
                    let utf8 = offers_utf8 params
                    let c2 = Caps c.fs c.proc c.sched c.out c.shared c.ckc c.flags utf8
                    reply (rpc.response id (capabilities utf8)) c2
                    serve input (Server [] 0 [] False) c2
                (Some "exit", _)             -> (Failure 1, input)
                (_, Some id)                 ->
                    reply (rpc.error_response id (0 - 32002) "the server is not initialized") c
                    begin input c
                _                            -> begin input c

# `checkers lsp`: serve on standard input and output, running `ckc` (with
# `flags`, a package's) for checks. `main` is a behaviour on its own fiber
# (D123), so the checks' behaviours run while this loop waits for input.
export partial fn run ckc flags term fs p sched -> code : ckc~String, flags~List String, term~Term, fs~Fs, p~Proc,
                                                          sched~Sched, code~ExitCode
    let out = cown.new (terminal.stdout term) sched
    let shared = cown.new (Shared [] [] []) sched
    let c = Caps fs p sched out shared ckc flags False
    let (code, rest) = begin (terminal.stdin term) c
    files.close rest
    code
