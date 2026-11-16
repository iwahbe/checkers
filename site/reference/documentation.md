# Documentation comments

Comments in particular places are documentation: the language server shows them on hover, and `checkers doc` turns them into a package's pages. Their text is Markdown (CommonMark), their links can name declarations, and their code is compiled, so an example in documentation can't go stale.

## Descriptions

- A **module's description** is the comment that opens its file, before the `module` line. If its first line has the form `NAME.ck — Text`, the description starts with `Text`.
- A **declaration's description** is the run of comment lines directly above it, with no blank line in between. The same goes for a record's field and an enum's constructor, from the lines above its own line.

Each line's `#` and the one space after it are removed, and the rest is Markdown.

```checkers
# Shapes and their areas.
module shapes

# A plane figure.
export enum Shape
    # A circle of radius `r`.
    Circle r : r~Nat
    # A rectangle `w` wide and `h` high.
    Rect w h : w~Nat, h~Nat

# The area of `s`, with π taken as 3; see [Shape].
export fn area s -> a : s~Shape, a~Nat
    match s
        Circle r -> 3 * r * r
        Rect w h -> w * h
```

## Links

In a description, `[name]` and `` [`name`] `` (shown as code) link to the documentation of a declaration, a module, or a constructor or field (`Type.name`). The name is resolved as the compiler resolves names in the module: its own declarations, its imports (`[list.sort]`, `[std.list.sort]`), and the prelude. A link that names nothing is W030; a link to something that isn't exported, so has no documentation, is W031. A link reference definition of the same label (`[name]: https://…`) takes precedence, and bracketed text that isn't a name (`[0]`, `[x, y]`) is just text; write `\[` for a bracket that would otherwise be read as a link.

## Code in documentation

A fenced code block (```` ``` ```` or `~~~`) whose info string is empty or starts with `checkers`, and an indented code block (four spaces in from the text), is Checkers code. It is compiled whenever the module is checked, and must compile without errors or warnings: each diagnostic it has is reported as W032, at its place in the comment. A block in another language says so (```` ```sh ````, ```` ```text ````) and is left alone.

```checkers
# The integer square root of `n`:
#
#     check isqrt 17 == 4
#     check isqrt 0 == 0
module roots

export fn isqrt n -> r : n~Nat, r~Nat, r * r <= n, n < (r + 1) * (r + 1)
    decreasing n
    if n < 2
        n
    else
        let s = isqrt (n / 4) * 2
        if (s + 1) * (s + 1) <= n then s + 1 else s
```

Each block is a module of its own, in the same program as the module it documents, so it may import that program's modules. A block without a `module` line is given one. A block in a module's doc comments **imports that module**, with every name it exports, unless the block imports it itself: the example above uses `isqrt` without an import.

**Hidden lines.** A line starting with `#!` is compiled but not shown: the documentation leaves it out. Hidden lines give an example the imports or definitions it needs without cluttering it.

```text
#     #! import std.list
#     check list.length [1, 2] == 2
```

**Attributes**, after `checkers` and separated by commas, change how a fenced block is treated:

| Info string | Treatment |
|---|---|
| `checkers` | compiled; run if it has `main` |
| `checkers,no_run` | compiled, not run |
| `checkers,ignore` | highlighted, neither compiled nor run |
| `checkers,compile_fail` | must not compile (W033 if it does) |
| `checkers,compile_fail,E0450` | must fail with that error among its errors (W033 otherwise) |

An indented block can't carry attributes; fence a block that needs them.

**Running.** `checkers doc` and `checkers site` also run each block that has `main` (with no arguments, no input and one thread), and show its output after it; a block whose `main` doesn't exit with `Success` is W034. A `compile_fail` block is shown with the compiler's report.

## Pages

A package's `README.md` and the pages of a site are Markdown too, with the same links and code blocks. Their blocks are modules of the package (or freestanding, for a site), and may import each other: every block of a page is compiled together. They import nothing implicitly.
