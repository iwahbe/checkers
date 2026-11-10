# packages.ck — a package's dependencies (SPEC §16.4, D108, D111): path
# dependencies, git dependencies fetched into the cache, minimal version
# selection, `checkers.lock`, and the `--package`/`--uses` flags for `ckc`.

module ck.packages

import std.system (Env, Proc)
import std.terminal (Term)
import std.files (Fs)
import std.env
import std.proc
import std.string
import std.bytes
import std.list (contains, reverse)
import ck.manifest (Version, Source, Git, Path, Dep, Manifest, Locked, Pinned, PinnedGit, PinnedPath)

# What resolving needs.
export record Caps
    fs~Fs
    env~Env
    proc~Proc
    term~Term

# A package of the build: its directory and the packages it may import.
export record Package
    name~String
    dir~String
    uses~List String
    pin~Pinned

# ── Paths ────────────────────────────────────────────────────────────────────

partial fn split b i start acc -> r : b~Bytes, i~Nat, start~Nat, acc~List String, r~List String
    if i >= len b
        reverse (piece b start (len b) :: acc)
    else if b[i] == '/'
        split b (i + 1) (i + 1) (piece b start i :: acc)
    else
        split b (i + 1) start acc

partial fn piece b i j -> s : b~Bytes, i~Nat, j~Nat, s~String
    if i <= j and j <= len b
        match string.from_utf8 (bytes.slice b i j)
            Some s -> s
            None   -> ""
    else
        ""

# Drop `.` and empty parts; `x/..` cancels.
partial fn tidy parts kept -> r : parts~List String, kept~List String, r~List String
    match parts
        []        -> reverse kept
        p :: rest ->
            if p == "." or p == ""
                tidy rest kept
            else if p == ".."
                match kept
                    k :: ks -> if k == ".." then tidy rest (p :: kept) else tidy rest ks
                    []      -> tidy rest [p]
            else
                tidy rest (p :: kept)

fn absolute s : s~String
    let b = string.bytes s
    len b > 0 and b[0] == '/'

# `d` relative to `base`, tidied.
export partial fn join base d -> r : base~String, d~String, r~String
    let whole = if absolute d then d else base ++ "/" ++ d
    let parts = tidy (split (string.bytes whole) 0 0 []) []
    let body = list.join "/" parts
    if absolute whole then "/" ++ body else if body == "" then "." else body

# ── Running programs ─────────────────────────────────────────────────────────

partial fn run program args c -> ok : program~String, args~List String, c~Caps, ok~Bool
    match proc.exec program args c.proc
        Ok n  -> n == 0
        Err _ -> False

partial fn exists dir c -> r : dir~String, c~Caps, r~Bool
    match files.list dir c.fs
        Ok _  -> True
        Err _ -> False

# The first line of a file.
partial fn first_line b i -> r : b~Bytes, i~Nat, r~Nat
    if i < len b and b[i] != '\n' and b[i] != '\r' then first_line b (i + 1) else i

partial fn read_line path c -> r : path~String, c~Caps, r~Option String
    match files.read path c.fs
        Ok b  ->
            let s = piece b 0 (first_line b 0)
            if s == "" then None else Some s
        Err _ -> None

# ── Git ──────────────────────────────────────────────────────────────────────

# `$XDG_CACHE_HOME/checkers/packages`, else `~/.cache/…`.
export partial fn cache c -> r : c~Caps, r~Result String String
    match env.get "XDG_CACHE_HOME" c.env
        Some d -> if d != "" then Ok (d ++ "/checkers/packages") else home c
        None   -> home c

partial fn home c -> r : c~Caps, r~Result String String
    match env.get "HOME" c.env
        Some h -> Ok (h ++ "/.cache/checkers/packages")
        None   -> Err "neither XDG_CACHE_HOME nor HOME is set, so there is nowhere to keep git dependencies"

fn tag v -> s : v~Version, s~String
    "v" ++ manifest.show v

# The last line of `b` that isn't empty.
partial fn last_line b -> s : b~Bytes, s~String
    let stop = trimmed b (len b)
    piece b (line_start b stop) stop

partial fn trimmed b j -> r : b~Bytes, j~Nat, r~Nat
    if j > 0 and j <= len b and (b[j - 1] == '\n' or b[j - 1] == '\r') then trimmed b (j - 1) else j

partial fn line_start b j -> r : b~Bytes, j~Nat, r~Nat
    if j > 0 and j <= len b and b[j - 1] != '\n' then line_start b (j - 1) else j

# Run git: the first line of its output, or what it said went wrong.
partial fn git args c -> r : args~List String, c~Caps, r~Result String String
    match proc.run "git" args b"" c.proc
        Err e -> Err ("can't run git: " ++ files.describe e)
        Ok o  ->
            if o.code == 0
                Ok (piece o.stdout 0 (first_line o.stdout 0))
            else
                Err (last_line o.stderr)

# Clone `url` into `tmp` (replacing whatever is there) and check out `rev`.
partial fn clone url rev tmp c -> r : url~String, rev~String, tmp~String, c~Caps, r~Result String String
    if not (run "rm" ["-rf", tmp] c)
        Err ("can't remove " ++ tmp)
    else
        match git ["clone", "--quiet", url, tmp] c
            Err e -> Err e
            Ok _  -> git ["-C", tmp, "-c", "advice.detachedHead=false", "checkout", "--quiet", rev] c

# `name` at version `v`: its directory and commit. `known` is the commit if
# the lock file or the cache already says which it is.
export partial fn fetch name url v known c -> r : name~String, url~String, v~Version, known~Option String,
                                                  c~Caps, r~Result (String, String) String
    match cache c
        Err e    -> Err e
        Ok cache ->
            let base = cache ++ "/" ++ name
            let remembered = base ++ "/" ++ tag v ++ ".commit"
            let commit = match known
                Some k -> Some k
                None   -> read_line remembered c
            match commit
                Some k ->
                    let dir = base ++ "/" ++ k
                    if exists dir c
                        Ok (dir, k)
                    else
                        fetch_into name url v k base c
                None   -> fetch_tag name url v base remembered c

partial fn announce name url v c -> r : name~String, url~String, v~Version, c~Caps, r~Unit
    terminal.eprint_line ("checkers: fetching " ++ name ++ " " ++ manifest.show v ++ " from " ++ url) c.term

partial fn fetch_into name url v k base c -> r : name~String, url~String, v~Version, k~String,
                                                 base~String, c~Caps, r~Result (String, String) String
    let tmp = base ++ "/.fetching"
    announce name url v c
    if not (run "mkdir" ["-p", base] c)
        Err ("can't create " ++ base)
    else
        match clone url k tmp c
            Err e -> Err ("could not fetch `" ++ name ++ "` at commit " ++ k ++ " from " ++ url ++ ": " ++ e)
            Ok _  ->
                if run "mv" [tmp, base ++ "/" ++ k] c
                    Ok (base ++ "/" ++ k, k)
                else
                    Err ("could not move `" ++ name ++ "` into " ++ base ++ "/" ++ k)

partial fn fetch_tag name url v base remembered c -> r : name~String, url~String, v~Version,
                                                         base~String, remembered~String, c~Caps,
                                                         r~Result (String, String) String
    let tmp = base ++ "/.fetching"
    announce name url v c
    if not (run "mkdir" ["-p", base] c)
        Err ("can't create " ++ base)
    else
        match clone url "HEAD" tmp c
            Err e -> Err ("could not fetch `" ++ name ++ "` from " ++ url ++ ": " ++ e)
            Ok _  ->
                match git ["-C", tmp, "rev-parse", "--verify", "--quiet", "refs/tags/" ++ tag v ++ "^{commit}"] c
                    Err _ ->
                        let _ = run "rm" ["-rf", tmp] c
                        Err ("`" ++ name ++ "`: " ++ url ++ " has no tag " ++ tag v)
                    Ok k  ->
                        match git ["-C", tmp, "-c", "advice.detachedHead=false", "checkout", "--quiet", k] c
                            Err e -> Err ("`" ++ name ++ "`: can't check out " ++ tag v ++ ": " ++ e)
                            Ok _  -> settle name tmp base k remembered c

# Move a checkout into the cache under its commit, and remember the tag's commit.
partial fn settle name tmp base k remembered c -> r : name~String, tmp~String, base~String, k~String,
                                                      remembered~String, c~Caps, r~Result (String, String) String
    let dir = base ++ "/" ++ k
    let placed = if exists dir c then run "rm" ["-rf", tmp] c else run "mv" [tmp, dir] c
    if placed
        let _ = files.write remembered (string.bytes (k ++ "\n")) c.fs
        Ok (dir, k)
    else
        Err ("could not move `" ++ name ++ "` into " ++ dir)

# ── Resolution ───────────────────────────────────────────────────────────────

# A dependency to visit: as declared, with the directory of the manifest
# that declares it and the package that does.
record Need
    dep~Dep
    base~String
    by~String

# A package version reached: where it is, and its manifest.
record Node
    name~String
    dir~String
    pin~Pinned
    man~Manifest
    by~String

# Where a dependency comes from, to tell two sources with one name apart.
partial fn origin d base -> s : d~Dep, base~String, s~String
    match d.source
        Git url _ -> url
        Path p    -> join base p

partial fn version_of p -> r : p~Pinned, r~Option Version
    match p
        PinnedGit _ v _ -> Some v
        PinnedPath _    -> None

# Has this version of this package been visited?
partial fn visited nodes name p -> r : nodes~List Node, name~String, p~Pinned, r~Bool
    match nodes
        []        -> False
        n :: rest -> (n.name == name and same n.pin p) or visited rest name p

partial fn same a b -> r : a~Pinned, b~Pinned, r~Bool
    match (a, b)
        (PinnedGit _ v _, PinnedGit _ w _) -> v == w
        (PinnedPath x, PinnedPath y)       -> x == y
        _                                  -> False

# The source another node with this name came from, if it differs.
partial fn clash nodes name o -> r : nodes~List Node, name~String, o~String, r~Option Node
    match nodes
        []        -> None
        n :: rest -> if n.name == name and pin_origin n.pin != o then Some n else clash rest name o

partial fn pin_origin p -> s : p~Pinned, s~String
    match p
        PinnedGit u _ _ -> u
        PinnedPath d    -> d

partial fn locked lock name url v -> r : lock~List Locked, name~String, url~String, v~Version, r~Option String
    match lock
        []        -> None
        l :: rest ->
            match l.pin
                PinnedGit u w k -> if l.name == name and u == url and w == v then Some k else locked rest name url v
                PinnedPath _    -> locked rest name url v

export partial fn read_manifest dir c -> r : dir~String, c~Caps, r~Result Manifest String
    let path = if dir == "." then "checkers.json" else dir ++ "/checkers.json"
    match files.read path c.fs
        Err e   -> Err (path ++ ": " ++ files.describe e)
        Ok text ->
            match manifest.read text
                Ok m  -> Ok m
                Err p -> Err (manifest.describe path text p)

partial fn needs m base -> r : m~Manifest, base~String, r~List Need
    list.map (\d -> Need d base m.name) m.deps

# This `checkers`'s version: a package's `toolchain` may not be newer.
export let TOOLCHAIN = Version 0 1 0

# Visit every package version reached from `todo` (Go's minimal version
# selection reads every manifest it reaches).
partial fn visit todo nodes lock c -> r : todo~List Need, nodes~List Node, lock~List Locked, c~Caps,
                                          r~Result (List Node) String
    match todo
        []        -> Ok nodes
        n :: rest ->
            let name = n.dep.name
            let o = origin n.dep n.base
            match clash nodes name o
                Some other -> Err ("two packages are called `" ++ name ++ "`: " ++ pin_origin other.pin ++ " (for `" ++ other.by ++ "`) and " ++ o ++ " (for `" ++ n.by ++ "`)")
                None       ->
                    match place n lock c
                        Err e       -> Err e
                        Ok (dir, p) ->
                            if visited nodes name p
                                visit rest nodes lock c
                            else
                                match read_manifest dir c
                                    Err e -> Err e
                                    Ok m  ->
                                        if m.name != name
                                            Err (dir ++ " is the package `" ++ m.name ++ "`, but `" ++ n.by ++ "` calls it `" ++ name ++ "`: a dependency's name must be its package's name")
                                        else if manifest.older TOOLCHAIN m.toolchain
                                            Err ("`" ++ name ++ "` needs checkers " ++ manifest.show m.toolchain ++ " or newer; this is " ++ manifest.show TOOLCHAIN)
                                        else
                                            visit (rest ++ needs m dir) (Node name dir p m n.by :: nodes) lock c

# Where the needed package is, fetching it if it's from git.
partial fn place n lock c -> r : n~Need, lock~List Locked, c~Caps, r~Result (String, Pinned) String
    match n.dep.source
        Path p    ->
            let dir = join n.base p
            Ok (dir, PinnedPath dir)
        Git url v ->
            match fetch n.dep.name url v (locked lock n.dep.name url v) c
                Ok (dir, k) -> Ok (dir, PinnedGit url v k)
                Err e       -> Err e

# `1.0.0 (by `shared`)`.
partial fn shown_at n -> s : n~Node, s~String
    match version_of n.pin
        Some v -> manifest.show v ++ " (by `" ++ n.by ++ "`)"
        None   -> pin_origin n.pin ++ " (by `" ++ n.by ++ "`)"

# The chosen node for `name`: the highest version reached (git), or the
# only one (path). An error if two major versions are needed.
partial fn choose nodes name best -> r : nodes~List Node, name~String, best~Option Node, r~Result Node String
    match nodes
        []        ->
            match best
                Some b -> Ok b
                None   -> Err ("internal: no package `" ++ name ++ "`")
        n :: rest ->
            if n.name != name
                choose rest name best
            else
                match best
                    None   -> choose rest name (Some n)
                    Some b ->
                        match (version_of n.pin, version_of b.pin)
                            (Some v, Some w) ->
                                if v.major != w.major
                                    let (lo, hi) = if manifest.older v w then (n, b) else (b, n)
                                    Err ("`" ++ name ++ "` is needed at two major versions: " ++ shown_at lo ++ " and " ++ shown_at hi)
                                else if manifest.older w v
                                    choose rest name (Some n)
                                else
                                    choose rest name best
                            _                -> choose rest name best

fn dep_name d -> s : d~Dep, s~String
    d.name

partial fn has ps name -> r : ps~List Package, name~String, r~Bool
    match ps
        []        -> False
        p :: rest -> p.name == name or has rest name

# The packages of the build: reached from the root through the chosen
# versions only.
partial fn build_list todo nodes acc -> r : todo~List String, nodes~List Node, acc~List Package,
                                            r~Result (List Package) String
    match todo
        []           -> Ok acc
        name :: rest ->
            if has acc name
                build_list rest nodes acc
            else
                match choose nodes name None
                    Err e -> Err e
                    Ok n  ->
                        let uses = list.map dep_name n.man.deps
                        build_list (rest ++ uses) nodes (Package name n.dir uses n.pin :: acc)

# The root package's manifest, its lock file, and its packages.
export record Build
    root~Manifest
    packages~List Package

partial fn read_lock c -> r : c~Caps, r~Result (List Locked) String
    match files.read "checkers.lock" c.fs
        Err _   -> Ok []
        Ok text ->
            match manifest.read_lock text
                Ok ls -> Ok ls
                Err p -> Err (manifest.describe "checkers.lock" text p)

partial fn insert p sorted -> r : p~Locked, sorted~List Locked, r~List Locked
    match sorted
        []        -> [p]
        q :: rest -> if string_less p.name q.name then p :: sorted else q :: insert p rest

partial fn string_less a b -> r : a~String, b~String, r~Bool
    bytes_less (string.bytes a) (string.bytes b) 0

partial fn bytes_less a b i -> r : a~Bytes, b~Bytes, i~Nat, r~Bool
    if i >= len b
        False
    else if i >= len a
        True
    else if a[i] != b[i]
        a[i] < b[i]
    else
        bytes_less a b (i + 1)

partial fn pins ps acc -> r : ps~List Package, acc~List Locked, r~List Locked
    match ps
        []        -> acc
        p :: rest -> pins rest (insert (Locked p.name p.pin) acc)

# Write `checkers.lock` if it changed.
partial fn write_lock ps c -> r : ps~List Package, c~Caps, r~Result Unit String
    let text = string.bytes (manifest.render_lock (pins ps []))
    let old = match files.read "checkers.lock" c.fs
        Ok b  -> b
        Err _ -> b""
    if old == text
        Ok ()
    else
        match files.write "checkers.lock" text c.fs
            Ok _  -> Ok ()
            Err e -> Err ("checkers.lock: " ++ files.describe e)

# Read `checkers.json` in the current directory, resolve and fetch its
# dependencies, and update `checkers.lock`.
export partial fn resolve c -> r : c~Caps, r~Result Build String
    match read_manifest "." c
        Err e -> Err e
        Ok m  ->
            if manifest.older TOOLCHAIN m.toolchain
                Err ("this package needs checkers " ++ manifest.show m.toolchain ++ " or newer; this is " ++ manifest.show TOOLCHAIN)
            else
                match read_lock c
                    Err e   -> Err e
                    Ok lock ->
                        match visit (needs m ".") [] lock c
                            Err e    -> Err e
                            Ok nodes ->
                                match build_list (list.map dep_name m.deps) nodes []
                                    Err e -> Err e
                                    Ok ps ->
                                        let ps = reverse ps
                                        match write_lock ps c
                                            Err e -> Err e
                                            Ok _  -> Ok (Build m ps)

partial fn package_flags ps -> r : ps~List Package, r~List String
    match ps
        []        -> []
        p :: rest -> ["--package", p.name ++ "=" ++ p.dir] ++ uses_flag p.name p.uses ++ package_flags rest

fn uses_flag name uses -> r : name~String, uses~List String, r~List String
    match uses
        [] -> []
        _  -> ["--uses", name ++ "=" ++ list.join "," uses]

# The flags that tell `ckc` about the build's packages (D111).
export partial fn flags b -> r : b~Build, r~List String
    package_flags b.packages ++ uses_flag "." (list.map dep_name b.root.deps)
