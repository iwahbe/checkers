# doc.ck — `checkers doc` and `checkers site` (SPEC §15.6, D131): a
# package's documentation, and the language's site, each page as Markdown
# and as HTML rendered from it.

module doc

import std.system (ExitCode, Proc)
import std.terminal (Term)
import std.terminal
import std.files (Fs, Entry)
import std.files
import std.proc
import std.json (Json, Null, Str, Arr)
import std.string
import std.bytes
import std.list
import ck.jsonrpc as rpc
import ck.markdown as md

export let USAGE = string.concat [
    "usage: checkers doc DIR -o OUT [--name NAME] [--root PATH] [--label TEXT]\n",
    "       checkers site SRC -o OUT\n\n",
    "`doc` documents the package in DIR (every .ck file under it): OUT/NAME/index and\n",
    "OUT/NAME/MODULE, each as .md and .html. NAME defaults to DIR's name; PATH is the\n",
    "way from those pages to the site's root (default ../..); TEXT names the version.\n",
    "`site` renders each SRC/PAGE.md to OUT/PAGE.md and OUT/PAGE.html, and writes\n",
    "OUT/llms.txt, a list of every Markdown page under OUT."]

# ── Paths ────────────────────────────────────────────────────────────────────

fn ends_with s suffix : s~String, suffix~String
    let b = string.bytes s
    let x = string.bytes suffix
    len x <= len b and bytes.matches_at b (len b - len x) x

fn hidden name : name~String
    let b = string.bytes name
    len b > 1 and b[0] == '.'

fn join_path dir name -> p : dir~String, name~String, p~String
    if dir == "." then name else dir ++ "/" ++ name

fn as_string b -> s : b~Bytes, s~String
    match string.from_utf8 b
        Some s -> s
        None   -> ""

# The last part of a path.
partial fn base_name path -> r : path~String, r~String
    let b = string.bytes (trim_slash path)
    as_string (bytes.slice b (after_slash b (len b)) (len b))

partial fn after_slash b i -> r : b~Bytes, i~Nat, i <= len b, r~Nat, r <= len b
    if i == 0 then 0 else if b[i - 1] == '/' then i else after_slash b (i - 1)

partial fn trim_slash path -> r : path~String, r~String
    let b = string.bytes path
    if len b > 1 and b[len b - 1] == '/' then trim_slash (as_string (bytes.slice b 0 (len b - 1))) else path

# The files under `dir` whose names end with `suffix`, sorted, as paths
# below `dir` (`a/b.ck`).
partial fn files_under dir rel suffix fs -> r : dir~String, rel~String, suffix~String, fs~Fs, r~List String
    match files.list (join_path dir rel) fs
        Ok es -> entries dir rel suffix es fs
        Err _ -> []

partial fn entries dir rel suffix es fs -> r : dir~String, rel~String, suffix~String, es~List Entry, fs~Fs,
                                               r~List String
    match es
        []        -> []
        e :: rest ->
            let path = join_path rel e.name
            let here = if e.dir and not (hidden e.name)
                files_under dir path suffix fs
            else if not e.dir and ends_with e.name suffix
                [path]
            else
                []
            here ++ entries dir rel suffix rest fs

# ── Pages ────────────────────────────────────────────────────────────────────

let STYLE = string.concat [
    ":root{--fg:#1d1f21;--muted:#5c6166;--bg:#fdfdfc;--panel:#f3f2ee;--line:#dedcd5;--accent:#8a3324;",
    "--kw:#8a3324;--ty:#1f5f8b;--st:#3d6b2e;--nu:#7a4f9a;--co:#7c7f84}",
    "@media (prefers-color-scheme:dark){:root{--fg:#e6e4df;--muted:#a3a19b;--bg:#17181a;--panel:#212226;",
    "--line:#34363b;--accent:#e08a6f;--kw:#e08a6f;--ty:#7fb4dd;--st:#a3c98b;--nu:#c9a3e0;--co:#8b8e94}}",
    "*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);",
    "font:16px/1.6 -apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif}",
    "header{border-bottom:1px solid var(--line);padding:12px 16px}",
    "header nav{max-width:820px;margin:0 auto;display:flex;gap:18px;align-items:baseline;flex-wrap:wrap}",
    "header a{color:var(--fg);text-decoration:none}header .home{font-weight:700}",
    "header .label{color:var(--muted);font-size:14px;margin-left:auto}",
    "main{max-width:820px;margin:0 auto;padding:16px 16px 64px}",
    "h1,h2,h3{line-height:1.25;margin:1.6em 0 .5em}h1{font-size:2em;margin-top:.6em}",
    "h2{font-size:1.4em;border-bottom:1px solid var(--line);padding-bottom:.2em}h3{font-size:1.15em}",
    "a{color:var(--accent)}code{font:14px/1.5 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}",
    ":not(pre)>code{background:var(--panel);padding:.1em .3em;border-radius:4px}",
    "pre{background:var(--panel);border:1px solid var(--line);border-radius:6px;padding:12px 14px;",
    "overflow-x:auto}pre code{white-space:pre}",
    ".kw{color:var(--kw);font-weight:600}.ty{color:var(--ty)}.st{color:var(--st)}.nu{color:var(--nu)}",
    ".co{color:var(--co);font-style:italic}",
    "table{border-collapse:collapse;display:block;overflow-x:auto}th,td{border:1px solid var(--line);",
    "padding:6px 10px;text-align:left;vertical-align:top}th{background:var(--panel)}",
    "blockquote{margin:1em 0;padding:0 1em;border-left:3px solid var(--line);color:var(--muted)}",
    "footer{max-width:820px;margin:0 auto;padding:16px;color:var(--muted);font-size:14px;",
    "border-top:1px solid var(--line)}"]

# An HTML page for Markdown `text`, saved as `name`.md beside it; `root` is
# the way from it to the site's root ("" or ending in `/`).
partial fn page text name root label -> r : text~Bytes, name~String, root~String, label~String, r~Bytes
    let title = match md.title text
        Some t -> as_string t
        None   -> name
    # A browser shows the title as text: no code marks.
    let plain = string.concat_map (\c -> if c == c'`' then "" else string.from_char c) title
    let page_title = if plain == "Checkers" then "Checkers" else plain ++ " · Checkers"
    let tag = if label == "" then "" else "<span class=\"label\">" ++ as_string (md.escape (string.bytes label)) ++ "</span>"
    let head = string.concat [
        "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n",
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
        "<title>", as_string (md.escape (string.bytes page_title)), "</title>\n",
        "<link rel=\"alternate\" type=\"text/markdown\" href=\"", name, ".md\">\n",
        "<style>", STYLE, "</style>\n</head>\n<body>\n<header><nav>",
        "<a class=\"home\" href=\"", root, "index.html\">Checkers</a>",
        "<a href=\"", root, "tour.html\">Tour</a>",
        "<a href=\"", root, "docs.html\">Documentation</a>",
        "<a href=\"https://github.com/iwahbe/checkers\">Source</a>", tag,
        "</nav></header>\n<main>\n"]
    let foot = string.concat [
        "</main>\n<footer>This page as Markdown: <a href=\"", name, ".md\">", name, ".md</a>. ",
        "Every page: <a href=\"", root, "llms.txt\">llms.txt</a>.</footer>\n</body>\n</html>\n"]
    bytes.concat [string.bytes head, md.to_html text, string.bytes foot]

# Write `name`.md and `name`.html into `dir`.
partial fn write_page dir name text root label fs -> r : dir~String, name~String, text~Bytes, root~String,
                                                         label~String, fs~Fs, r~Result Unit String
    match files.write (join_path dir (name ++ ".md")) text fs
        Err e -> Err (join_path dir (name ++ ".md") ++ ": " ++ files.describe e)
        Ok _  ->
            match files.write (join_path dir (name ++ ".html")) (page text name root label) fs
                Err e -> Err (join_path dir (name ++ ".html") ++ ": " ++ files.describe e)
                Ok _  -> Ok ()

# ── `checkers doc` ───────────────────────────────────────────────────────────

# A declaration or one of its constructors or fields, as `ckc doc` gives it.
record Item
    what~String
    name~String
    signature~String
    doc~String
    items~List Item

record Module
    name~String
    doc~String
    decls~List Item

partial fn str key j -> s : key~String, j~Json, s~String
    match rpc.str_at [key] j
        Some s -> s
        None   -> ""

partial fn item_of j -> i : j~Json, i~Item
    let items = match rpc.get "items" j
        Some (Arr xs) -> list.map item_of xs
        _             -> []
    Item (str "what" j) (str "name" j) (str "signature" j) (str "doc" j) items

partial fn module_of lines m -> r : lines~List Bytes, m~Module, r~Module
    match lines
        []        -> Module m.name m.doc (list.reverse m.decls)
        l :: rest ->
            match json.parse l
                Ok j  ->
                    if str "kind" j == "module"
                        module_of rest (Module (str "name" j) (str "doc" j) m.decls)
                    else if str "kind" j == "decl"
                        module_of rest (Module m.name m.doc (item_of j :: m.decls))
                    else
                        module_of rest m
                Err _ -> module_of rest m

# The module in `file`, as `ckc doc` reads it.
partial fn read_module ckc file p -> r : ckc~String, file~String, p~Proc, r~Result Module String
    match proc.run ckc ["doc", file] b"" p
        Err e  -> Err ("could not run `" ++ ckc ++ "`: " ++ files.describe e)
        Ok out ->
            let m = module_of (md.lines_of out.stdout) (Module "" "" [])
            if m.name == ""
                Err (file ++ ": `" ++ ckc ++ " doc` gave nothing (" ++ as_string out.stderr ++ ")")
            else
                Ok m

# A module's page name: its name without the package's (`std.list` → `list`).
partial fn page_name package name -> r : package~String, name~String, r~String
    let b = string.bytes name
    let prefix = string.bytes (package ++ ".")
    if bytes.matches_at b 0 prefix then as_string (bytes.slice b (len prefix) (len b)) else name

# The first sentence of a description, on one line.
partial fn first_sentence doc -> r : doc~String, r~String
    let b = string.bytes doc
    as_string (one_line (bytes.slice b 0 (sentence_end b 0)))

partial fn sentence_end b i -> r : b~Bytes, i~Nat, i <= len b, r~Nat, r <= len b
    if i >= len b
        len b
    else if b[i] == '\n' and i + 1 < len b and b[i + 1] == '\n'
        i
    else if b[i] == '.' and (i + 1 == len b or b[i + 1] == ' ' or b[i + 1] == '\n')
        i + 1
    else
        sentence_end b (i + 1)

partial fn one_line b -> r : b~Bytes, r~Bytes
    bytes.concat (list.map (\l -> l) (spaced (md.lines_of b)))

partial fn spaced ls -> r : ls~List Bytes, r~List Bytes
    match ls
        []        -> []
        [x]       -> [x]
        x :: rest -> x :: b" " :: spaced rest

# `export ` is left out of a signature: everything documented is exported.
# Lines after the first move left with it, so what was aligned stays so.
partial fn shown sig -> r : sig~String, r~String
    let b = string.bytes sig
    if bytes.matches_at b 0 b"export "
        match md.lines_of (bytes.slice b 7 (len b))
            []          -> ""
            first :: ls -> as_string (bytes.concat (first :: list.map dedent ls))
    else
        sig

partial fn dedent l -> r : l~Bytes, r~Bytes
    if bytes.matches_at l 0 b"       " then bytes.concat [b"\n", bytes.slice l 7 (len l)] else bytes.concat [b"\n", l]

partial fn decl_md d -> r : d~Item, r~String
    let items = if d.items == []
        ""
    else
        let heading = if d.what == "record" then "Fields:\n\n" else "Constructors:\n\n"
        heading ++ string.concat (list.map item_md d.items) ++ "\n"
    let doc = if d.doc == "" then "" else d.doc ++ "\n\n"
    string.concat ["### ", d.what, " `", d.name, "`\n\n```checkers\n", shown d.signature, "\n```\n\n", doc, items]

partial fn item_md i -> r : i~Item, r~String
    let doc = if i.doc == "" then "" else ": " ++ one_line_str i.doc
    "- `" ++ i.signature ++ "`" ++ doc ++ "\n"

partial fn one_line_str s -> r : s~String, r~String
    as_string (one_line (string.bytes s))

partial fn index_md m -> r : m~Module, r~String
    if m.decls == []
        ""
    else
        "## Index\n\n" ++ string.concat (list.map index_line m.decls) ++ "\n"

partial fn index_line d -> r : d~Item, r~String
    let anchor = as_string (md.slug (string.bytes (d.what ++ " " ++ d.name)))
    "- [" ++ d.what ++ " `" ++ d.name ++ "`](#" ++ anchor ++ ")\n"

partial fn module_md package m -> r : package~String, m~Module, r~String
    let doc = if m.doc == "" then "" else m.doc ++ "\n\n"
    let body = if m.decls == []
        "It exports nothing.\n"
    else
        "## Declarations\n\n" ++ string.concat (list.map decl_md m.decls)
    string.concat [
        "# Module `", m.name, "`\n\nIn package [", package, "](index.md).\n\n", doc, index_md m, body]

partial fn package_md package ms -> r : package~String, ms~List Module, r~String
    let rows = list.map (\m -> string.concat [
        "| [", m.name, "](", page_name package m.name, ".md) | ", first_sentence m.doc, " |\n"]) ms
    string.concat ([
        "# Package `", package, "`\n\n",
        "Each module's page lists what it exports: signatures as written, with their conditions, ",
        "and descriptions.\n\n| Module | Description |\n|---|---|\n"] ++ rows)

partial fn read_all ckc dir rels p acc -> r : ckc~String, dir~String, rels~List String, p~Proc,
                                              acc~List Module, r~Result (List Module) String
    match rels
        []          -> Ok (list.reverse acc)
        rel :: rest ->
            match read_module ckc (join_path dir rel) p
                Err e -> Err e
                Ok m  -> read_all ckc dir rest p (m :: acc)

partial fn write_modules out package ms root label fs -> r : out~String, package~String, ms~List Module,
                                                             root~String, label~String, fs~Fs,
                                                             r~Result Unit String
    match ms
        []        -> Ok ()
        m :: rest ->
            let text = string.bytes (module_md package m)
            match write_page out (page_name package m.name) text root label fs
                Err e -> Err e
                Ok _  -> write_modules out package rest root label fs

record DocArgs
    dir~String
    out~String
    name~String
    root~String
    label~String

partial fn doc_args args a -> r : args~List String, a~DocArgs, r~Option DocArgs
    match args
        []                     -> if a.dir == "" or a.out == "" then None else Some a
        "-o" :: o :: rest      -> doc_args rest (DocArgs a.dir o a.name a.root a.label)
        "--name" :: n :: rest  -> doc_args rest (DocArgs a.dir a.out n a.root a.label)
        "--root" :: x :: rest  -> doc_args rest (DocArgs a.dir a.out a.name x a.label)
        "--label" :: x :: rest -> doc_args rest (DocArgs a.dir a.out a.name a.root x)
        d :: rest              -> if a.dir == "" then doc_args rest (DocArgs d a.out a.name a.root a.label) else None

fn fail message term -> code : message~String, term~Term, code~ExitCode
    terminal.eprint_line ("checkers: " ++ message) term
    Failure 1

partial fn with_slash root -> r : root~String, r~String
    if root == "" or ends_with root "/" then root else root ++ "/"

# `checkers doc DIR -o OUT [--name NAME] [--root PATH] [--label TEXT]`.
export partial fn run args ckc term fs p -> code : args~List String, ckc~String, term~Term, fs~Fs, p~Proc,
                                                   code~ExitCode
    match doc_args args (DocArgs "" "" "" "../.." "")
        None   ->
            terminal.eprint_line USAGE term
            Failure 2
        Some a ->
            let package = if a.name == "" then base_name a.dir else a.name
            let out = join_path a.out package
            let root = with_slash a.root
            match read_all ckc a.dir (files_under a.dir "." ".ck" fs) p []
                Err e -> fail e term
                Ok ms ->
                    match files.create_dirs out fs
                        Err e -> fail (out ++ ": " ++ files.describe e) term
                        Ok _  ->
                            let index = string.bytes (package_md package ms)
                            match write_page out "index" index root a.label fs
                                Err e -> fail e term
                                Ok _  ->
                                    match write_modules out package ms root a.label fs
                                        Err e -> fail e term
                                        Ok _  -> Success

# ── `checkers site` ──────────────────────────────────────────────────────────

partial fn strip_md name -> r : name~String, r~String
    let b = string.bytes name
    if ends_with name ".md" then as_string (bytes.slice b 0 (len b - 3)) else name

# The way from a page at `rel` (`docs/std/list.md`) to the site's root.
partial fn root_of rel -> r : rel~String, r~String
    string.concat (list.map (\x -> "../") (slashes (string.bytes rel) 0 []))

partial fn slashes b i acc -> r : b~Bytes, i~Nat, acc~List Nat, r~List Nat
    if i >= len b then acc else if b[i] == '/' then slashes b (i + 1) (i :: acc) else slashes b (i + 1) acc

partial fn render_pages src out pages fs -> r : src~String, out~String, pages~List String, fs~Fs,
                                                r~Result Unit String
    match pages
        []          -> Ok ()
        rel :: rest ->
            match files.read (join_path src rel) fs
                Err e   -> Err (join_path src rel ++ ": " ++ files.describe e)
                Ok text ->
                    match write_page out (strip_md rel) text (root_of rel) "" fs
                        Err e -> Err e
                        Ok _  -> render_pages src out rest fs

# The first paragraph after the first heading: the site's summary.
partial fn summary text -> r : text~Bytes, r~String
    as_string (one_line (first_paragraph (md.lines_of text) False []))

partial fn first_paragraph ls seen acc -> r : ls~List Bytes, seen~Bool, acc~List Bytes, r~Bytes
    match ls
        []        -> bytes.concat (list.reverse acc)
        l :: rest ->
            let empty = md.blank l
            if not seen
                first_paragraph rest (bytes.matches_at l 0 b"# ") acc
            else if empty and acc == []
                first_paragraph rest seen acc
            else if empty
                bytes.concat (list.reverse acc)
            else
                first_paragraph rest seen ((if acc == [] then l else bytes.concat [b"\n", l]) :: acc)

partial fn link_line out rel fs -> r : out~String, rel~String, fs~Fs, r~String
    let title = match files.read (join_path out rel) fs
        Ok text ->
            match md.title text
                Some t -> as_string t
                None   -> rel
        Err _   -> rel
    "- [" ++ title ++ "](" ++ rel ++ ")\n"

# The documentation `llms.txt` lists: the latest only (§15.6).
partial fn in_docs rel : rel~String
    bytes.matches_at (string.bytes rel) 0 b"docs/latest/"

partial fn only_docs rels -> r : rels~List String, r~List String
    match rels
        []        -> []
        x :: rest -> if in_docs x then x :: only_docs rest else only_docs rest

partial fn llms out pages index fs -> r : out~String, pages~List String, index~Bytes, fs~Fs, r~String
    let all = files_under out "." ".md" fs
    let docs = only_docs all
    let title = match md.title index
        Some t -> as_string t
        None   -> "Checkers"
    let head = string.concat [
        "# ", title, "\n\n> ", summary index, "\n\n",
        "Every page of this site is also Markdown: replace `.html` with `.md`.\n\n## Pages\n\n"]
    let listed = list.map (\r -> link_line out r fs) pages
    let documented = if docs == [] then [] else "\n## Documentation\n\n" :: list.map (\r -> link_line out r fs) docs
    string.concat (head :: listed ++ documented)

# `checkers site SRC -o OUT`.
export partial fn site args term fs -> code : args~List String, term~Term, fs~Fs, code~ExitCode
    match args
        [src, "-o", out] ->
            let pages = files_under src "." ".md" fs
            match files.create_dirs out fs
                Err e -> fail (out ++ ": " ++ files.describe e) term
                Ok _  ->
                    match render_pages src out pages fs
                        Err e -> fail e term
                        Ok _  ->
                            let index = match files.read (join_path src "index.md") fs
                                Ok t  -> t
                                Err _ -> b""
                            match files.write (join_path out "llms.txt") (string.bytes (llms out pages index fs)) fs
                                Err e -> fail ("llms.txt: " ++ files.describe e) term
                                Ok _  -> Success
        _                ->
            terminal.eprint_line USAGE term
            Failure 2
