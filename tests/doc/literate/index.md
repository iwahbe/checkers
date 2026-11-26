# Literate pages

Links name symbols: [std.list.sort], [`list.sort`] through the hidden import
below, [Option] and [Some] from the prelude, and [`Error.pos`], a field.
[std.list.merge_by] isn't exported, [nothing.here] isn't anything, and
[x, y] and [0] are only text. A definition wins: [sort].

[sort]: https://example.com/sort

```checkers
#! import std.list
#! import std.json (Error)
```

A block with `main` runs, and its output follows it:

```checkers
module hello

import std.system (System, ExitCode)
import std.terminal

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "hello from a block" sys.term
    Success
```

A block without a `module` line gets a hidden one; `#!` lines are compiled but
not shown:

```
#! import std.list
check list.length [1, 2, 3] == 3
```

```checkers,compile_fail,E0450
module wrong

fn last xs -> x : xs~Bytes, x~U8
    xs[len xs - 1]
```

Warnings: a block that compiles though it shouldn't, one that fails with
another error than it says, one with an error, and one whose `main` fails.

```checkers,compile_fail
module fine

check 1 + 1 == 2
```

```checkers,compile_fail,E0201
module other

fn f x -> y : x~Nat, y~Nat
    x - 1
```

```checkers
module broken

fn f x -> y : x~Nat, y~Nat
    "no"
```

```checkers
module failing

import std.system (System, ExitCode)

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    Failure 3
```

```checkers,no_run
module waits

import std.system (System, ExitCode)
import std.terminal

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    match terminal.read_line sys.term
        Ok (Some l) ->
            terminal.write_bytes l sys.term
            Success
        _           -> Failure 1
```

```checkers,ignore
fn only a signature -> r : r~Nat
```

```sh
checkers site docs -o out
```

| Attribute | Meaning |
|---|---|
| `compile_fail` | must not compile |
| `no_run` | compiled, not run |
