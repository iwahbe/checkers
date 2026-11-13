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
    "OUT/NAME/MODULE, each as .md and .html; DIR/README.md, if any, describes the package.\n",
    "NAME defaults to DIR's name; PATH is the way from those pages to the site's root\n",
    "(default ../..); TEXT names the version.\n",
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
    ".wide header nav{max-width:1160px}",
    "header a{color:var(--fg);text-decoration:none}header .home{font-weight:700}",
    "header select{margin-left:auto;font:inherit;font-size:14px;color:var(--fg);background:var(--panel);",
    "border:1px solid var(--line);border-radius:4px;padding:1px 4px}",
    "main{max-width:820px;margin:0 auto;padding:16px 16px 64px}",
    ".layout{max-width:1160px;margin:0 auto;display:grid;grid-template-columns:240px minmax(0,1fr)}",
    ".layout main{max-width:none;margin:0;min-width:0;padding-left:32px}",
    "nav.side{position:sticky;top:0;align-self:start;max-height:100vh;overflow-y:auto;",
    "padding:24px 16px;font-size:14px;border-right:1px solid var(--line)}",
    "nav.side .crumb{font:600 15px/1.4 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;margin-bottom:12px}",
    "nav.side ul{list-style:none;margin:0;padding:0}nav.side li{margin:3px 0}",
    "nav.side li a{color:var(--fg);text-decoration:none;font-family:ui-monospace,SFMono-Regular,Menlo,monospace}",
    "nav.side li a:hover{color:var(--accent)}nav.side .kind{color:var(--muted)}",
    "@media (max-width:760px){.layout{display:block}.layout main{padding-left:16px}",
    "nav.side{position:static;max-height:none;border-right:0;border-bottom:1px solid var(--line);padding:16px}",
    "nav.side ul{display:flex;flex-wrap:wrap;gap:2px 16px}nav.side li{margin:0}}",
    "h1,h2,h3{line-height:1.25;margin:1.6em 0 .5em}h1{font-size:2em;margin-top:.6em}",
    "h2{font-size:1.4em;border-bottom:1px solid var(--line);padding-bottom:.2em}h3{font-size:1.15em}",
    "a{color:var(--accent)}code{font:14px/1.5 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}",
    ":not(pre)>code{background:var(--panel);padding:.1em .3em;border-radius:4px}",
    "pre{background:var(--panel);border:1px solid var(--line);border-radius:6px;padding:12px 14px;",
    "overflow-x:auto}pre code{white-space:pre}pre a{color:inherit;text-decoration:none}",
    "pre a:hover{text-decoration:underline}",
    ".kw{color:var(--kw);font-weight:600}.ty{color:var(--ty)}.st{color:var(--st)}.nu{color:var(--nu)}",
    ".co{color:var(--co);font-style:italic}",
    "table{border-collapse:collapse;display:block;overflow-x:auto}th,td{border:1px solid var(--line);",
    "padding:6px 10px;text-align:left;vertical-align:top}th{background:var(--panel)}",
    "blockquote{margin:1em 0;padding:0 1em;border-left:3px solid var(--line);color:var(--muted)}"]

# The version menu (§15.6): the other versions come from docs/versions.json
# at the site's root; choosing one opens this page in it, or that version's
# package page if it has no such page.
let VERSIONS = string.concat [
    "<script>(function(){var s=document.querySelector('select.version');if(!s)return;",
    "var root=new URL(s.getAttribute('data-root')||'./',location.href);",
    "var rel=location.pathname.slice(root.pathname.length).split('/');if(rel[0]!=='docs'||rel.length<4)return;",
    "fetch(new URL('docs/versions.json',root)).then(function(r){return r.json()}).then(function(v){",
    "var names=['latest'].concat(v.versions||[]);s.textContent='';names.forEach(function(n){",
    "var o=document.createElement('option');o.value=n;o.textContent=n==='latest'?'latest ('+(v.latest||'dev')+')':n;",
    "if(n===rel[1])o.selected=true;s.appendChild(o)})}).catch(function(){});",
    "s.addEventListener('change',function(){var r=rel.slice();r[1]=s.value;var u=new URL(r.join('/'),root);",
    "var home=new URL(['docs',s.value,rel[2],'index.html'].join('/'),root);",
    "fetch(u,{method:'HEAD'}).then(function(x){location.href=x.ok?u:home}).catch(function(){location.href=home})})",
    "})();</script>\n"]

# A page: `body` (HTML) under the site's top bar, with the navigation column
# `side` (HTML) if it isn't empty. `title` is its Markdown title, `name` the
# Markdown twin beside it; `root` is the way to the site's root ("" or
# ending in `/`); `label`, if any, the version shown.
partial fn page title name root label side body -> r : title~String, name~String, root~String, label~String,
                                                       side~Bytes, body~Bytes, r~Bytes
    # A browser shows the title as text: no code marks.
    let plain = string.concat_map (\c -> if c == c'`' then "" else string.from_char c) title
    let page_title = if plain == "Checkers" then "Checkers" else plain ++ " · Checkers"
    let label_html = as_string (md.escape (string.bytes label))
    let menu = if label == ""
        ""
    else
        string.concat [
            "<select class=\"version\" aria-label=\"Version\" data-root=\"", root, "\"><option selected>",
            label_html, "</option></select>"]
    let wide = len side > 0
    let head = string.concat [
        "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n",
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
        "<title>", as_string (md.escape (string.bytes page_title)), "</title>\n",
        "<link rel=\"alternate\" type=\"text/markdown\" href=\"", name, ".md\">\n",
        "<link rel=\"describedby\" href=\"", root, "llms.txt\">\n",
        "<style>", STYLE, "</style>\n</head>\n<body", if wide then " class=\"wide\"" else "", ">\n<header><nav>",
        "<a class=\"home\" href=\"", root, "index.html\">Checkers</a>",
        "<a href=\"", root, "tour.html\">Tour</a>",
        "<a href=\"", root, "docs/latest/std/index.html\">Documentation</a>",
        "<a href=\"https://github.com/iwahbe/checkers\">Source</a>", menu, "</nav></header>\n"]
    let open = if wide then "<div class=\"layout\">\n<nav class=\"side\">\n" else ""
    let between = if wide then "</nav>\n<main>\n" else "<main>\n"
    let close = string.concat [if wide then "</main>\n</div>\n" else "</main>\n", if label == "" then "" else VERSIONS]
    bytes.concat [
        string.bytes head, string.bytes open, side, string.bytes between, body, string.bytes close,
        b"</body>\n</html>\n"]

# Write `name`.md (`text`) and `name`.html into `dir`.
partial fn write_page dir name text root label side body fs -> r : dir~String, name~String, text~Bytes, root~String,
                                                                   label~String, side~Bytes, body~Bytes, fs~Fs,
                                                                   r~Result Unit String
    let title = match md.title text
        Some t -> as_string t
        None   -> name
    match files.write (join_path dir (name ++ ".md")) text fs
        Err e -> Err (join_path dir (name ++ ".md") ++ ": " ++ files.describe e)
        Ok _  ->
            match files.write (join_path dir (name ++ ".html")) (page title name root label side body) fs
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

# An import: the module, the name it is used by, the names it brings in.
record Import
    source~String
    used~String
    names~List String

record Module
    name~String
    doc~String
    imports~List Import
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

partial fn strings js -> r : js~List Json, r~List String
    match js
        []            -> []
        Str s :: rest -> s :: strings rest
        _ :: rest     -> strings rest

partial fn import_of j -> i : j~Json, i~Import
    let names = match rpc.get "names" j
        Some (Arr xs) -> strings xs
        _             -> []
    Import (str "module" j) (str "as" j) names

partial fn module_of lines m -> r : lines~List Bytes, m~Module, r~Module
    match lines
        []        -> Module m.name m.doc (list.reverse m.imports) (list.reverse m.decls)
        l :: rest ->
            match json.parse l
                Ok j  ->
                    let kind = str "kind" j
                    if kind == "module"
                        module_of rest (Module (str "name" j) (str "doc" j) m.imports m.decls)
                    else if kind == "import"
                        module_of rest (Module m.name m.doc (import_of j :: m.imports) m.decls)
                    else if kind == "decl"
                        module_of rest (Module m.name m.doc m.imports (item_of j :: m.decls))
                    else
                        module_of rest m
                Err _ -> module_of rest m

# The module in `file`, as `ckc doc` reads it.
partial fn read_module ckc file p -> r : ckc~String, file~String, p~Proc, r~Result Module String
    match proc.run ckc ["doc", file] b"" p
        Err e  -> Err ("could not run `" ++ ckc ++ "`: " ++ files.describe e)
        Ok out ->
            let m = module_of (md.lines_of out.stdout) (Module "" "" [] [])
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

# A declaration's anchor on its module's page: its heading's.
partial fn anchor d -> r : d~Item, r~String
    as_string (md.slug (string.bytes (d.what ++ " " ++ d.name)))

# A field or constructor in its declaration's code block: its description
# as a comment above it.
partial fn item_code i -> r : i~Item, r~String
    let doc = if i.doc == "" then [] else list.map (\l -> comment_line l) (md.lines_of (string.bytes i.doc))
    string.concat (doc ++ ["\n    ", i.signature])

partial fn comment_line l -> r : l~Bytes, r~String
    if md.blank l then "\n    #" else "\n    # " ++ as_string l

partial fn decl_md d -> r : d~Item, r~String
    let doc = if d.doc == "" then "" else d.doc ++ "\n\n"
    let code = shown d.signature ++ string.concat (list.map item_code d.items)
    string.concat ["## ", d.what, " `", d.name, "`\n\n```checkers\n", code, "\n```\n\n", doc]

partial fn module_md m -> r : m~Module, r~String
    let doc = if m.doc == "" then "" else m.doc ++ "\n\n"
    let body = if m.decls == [] then "It exports nothing.\n" else string.concat (list.map decl_md m.decls)
    string.concat ["# Module `", m.name, "`\n\n", doc, body]

# A README's text without its first heading (the page has its own).
partial fn without_title ls -> r : ls~List Bytes, r~List Bytes
    match ls
        []        -> []
        l :: rest ->
            if md.blank l
                without_title rest
            else if bytes.matches_at l 0 b"# "
                drop_blank rest
            else
                ls

partial fn drop_blank ls -> r : ls~List Bytes, r~List Bytes
    match ls
        l :: rest -> if md.blank l then drop_blank rest else ls
        []        -> []

partial fn package_md package readme ms -> r : package~String, readme~Bytes, ms~List Module, r~String
    let rows = list.map (\m -> string.concat [
        "| [", m.name, "](", page_name package m.name, ".md) | ", first_sentence m.doc, " |\n"]) ms
    let about = list.map (\l -> as_string l ++ "\n") (without_title (md.lines_of readme))
    let about_text = if about == [] then "" else string.concat about ++ "\n"
    string.concat ([
        "# Package `", package, "`\n\n", about_text, "## Modules\n\n| Module | Description |\n|---|---|\n"]
                   ++ rows)

# ── Links ────────────────────────────────────────────────────────────────────

partial fn flatten xss -> r : xss~List (List a), r~List a
    match xss
        []         -> []
        xs :: rest -> xs ++ flatten rest

# A name a signature can link to: a type, or a constructor or constant (D26).
record Target
    home~String
    name~String
    anchor~String
    ty~Bool

partial fn targets_of m -> r : m~Module, r~List Target
    flatten (list.map (\d -> decl_targets m.name d) m.decls)

partial fn decl_targets owner d -> r : owner~String, d~Item, r~List Target
    let a = anchor d
    if d.what == "enum"
        Target owner d.name a True :: ctor_targets owner a d.items
    else if d.what == "record"
        [Target owner d.name a True, Target owner d.name a False]
    else if d.what == "type"
        [Target owner d.name a True]
    else if d.what == "let"
        [Target owner d.name a False]
    else if d.what == "class"
        Target owner d.name a True :: list.map (member_target owner a) d.items
    else
        []

# A class's function or lemma: a link to its class.
partial fn member_target owner a i -> r : owner~String, a~String, i~Item, r~Target
    Target owner i.name a False

partial fn ctor_targets owner a cs -> r : owner~String, a~String, cs~List Item, r~List Target
    match cs
        []        -> []
        c :: rest -> Target owner c.name a False :: ctor_targets owner a rest

# The modules an unqualified name may come from in `m`, in order: `m`, the
# imports that bring it in, the prelude.
partial fn sources m name -> r : m~Module, name~String, r~List String
    m.name :: (list.map (\i -> i.source) (bringing m.imports name) ++ ["std.prelude"])

partial fn bringing is name -> r : is~List Import, name~String, r~List Import
    match is
        []        -> []
        i :: rest -> if list.contains i.names name then i :: bringing rest name else bringing rest name

partial fn named is used -> r : is~List Import, used~String, r~List String
    match is
        []        -> []
        i :: rest -> if i.used == used then [i.source] else named rest used

partial fn find ts mods name ty -> r : ts~List Target, mods~List String, name~String, ty~Bool, r~Option Target
    match mods
        []          -> None
        mod :: rest ->
            match first_target ts mod name ty
                Some t -> Some t
                None   -> find ts rest name ty

partial fn first_target ts mod name ty -> r : ts~List Target, mod~String, name~String, ty~Bool, r~Option Target
    match ts
        []        -> None
        t :: rest -> if t.home == mod and t.name == name and t.ty == ty then Some t else first_target rest mod name ty

# Where `qual.name` in a signature of `m` leads (§15.6): within the package
# only; in a type, a type; elsewhere a constructor or constant, else a type.
partial fn resolve package ts m qual name ty -> r : package~String, ts~List Target, m~Module, qual~Bytes,
                                                    name~Bytes, ty~Bool, r~Option Bytes
    let n = as_string name
    let q = as_string qual
    let mods = if q == "" then sources m n else named m.imports q
    let found = if ty
        find ts mods n True
    else
        match find ts mods n False
            Some t -> Some t
            None   -> find ts mods n True
    match found
        Some t ->
            let page = if t.home == m.name then "" else page_name package t.home ++ ".html"
            Some (string.bytes (page ++ "#" ++ t.anchor))
        None   -> None

# ── Navigation ───────────────────────────────────────────────────────────────

partial fn esc s -> r : s~String, r~String
    as_string (md.escape (string.bytes s))

# `package.module`, `package` leading to the package's page.
partial fn crumb package name -> r : package~String, name~String, r~String
    let rest = page_name package name
    let tail = if name == "" then "" else if rest == name then " · " ++ esc name else "." ++ esc rest
    string.concat ["<div class=\"crumb\"><a href=\"index.html\">", esc package, "</a>", tail, "</div>\n"]

partial fn module_side package m -> r : package~String, m~Module, r~Bytes
    let line = \d -> string.concat [
        "<li><a href=\"#", anchor d, "\"><span class=\"kind\">", d.what, "</span> ", esc d.name, "</a></li>\n"]
    string.bytes (string.concat ([crumb package m.name, "<ul>\n"] ++ list.map line m.decls ++ ["</ul>\n"]))

partial fn package_side package ms -> r : package~String, ms~List Module, r~Bytes
    string.bytes (string.concat ([crumb package "", "<ul>\n"] ++ module_lines package ms ++ ["</ul>\n"]))

partial fn module_lines package ms -> r : package~String, ms~List Module, r~List String
    match ms
        []        -> []
        m :: rest ->
            let line = string.concat [
                "<li><a href=\"", page_name package m.name, ".html\">", esc (page_name package m.name), "</a></li>\n"]
            line :: module_lines package rest

partial fn read_all ckc dir rels p acc -> r : ckc~String, dir~String, rels~List String, p~Proc,
                                              acc~List Module, r~Result (List Module) String
    match rels
        []          -> Ok (list.reverse acc)
        rel :: rest ->
            match read_module ckc (join_path dir rel) p
                Err e -> Err e
                Ok m  -> read_all ckc dir rest p (m :: acc)

partial fn write_modules out package ts ms root label fs -> r : out~String, package~String, ts~List Target,
                                                                ms~List Module, root~String,
                                                                label~String, fs~Fs, r~Result Unit String
    match ms
        []        -> Ok ()
        m :: rest ->
            let text = string.bytes (module_md m)
            let body = md.to_html_linked text (\q n ty -> resolve package ts m q n ty)
            match write_page out (page_name package m.name) text root label (module_side package m) body fs
                Err e -> Err e
                Ok _  -> write_modules out package ts rest root label fs

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
                            let readme = match files.read (join_path a.dir "README.md") fs
                                Ok text -> text
                                Err _   -> b""
                            let index = string.bytes (package_md package readme ms)
                            let side = package_side package ms
                            match write_page out "index" index root a.label side (md.to_html index) fs
                                Err e -> fail e term
                                Ok _  ->
                                    let ts = flatten (list.map targets_of ms)
                                    match write_modules out package ts ms root a.label fs
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
                    match write_page out (strip_md rel) text (root_of rel) "" b"" (md.to_html text) fs
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
