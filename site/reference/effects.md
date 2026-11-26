# Capabilities and resources

A Checkers function is a mathematical function: called with the same arguments it gives the same result, and the prover relies on it. Effects (reading a file, printing, starting a process, scheduling work) are kept sound by **capabilities**: values that every effectful operation takes as an argument. Code can only do what it is handed a capability for, so a function's signature says which effects it can have: a JSON parser that is never given an `Fs` can't read files.

There are two kinds of capability:

| Kind | Types | Used |
|---|---|---|
| authority | `System`, `Term`, `Fs`, `Env`, `Proc`, `Net`, `Clock`, `Sched` | any number of times, and may go unused |
| resource | `File`, `Child`, and every type that holds one | exactly once on every path |

## `main`

A program is a module that exports `main`:

```text
export fn main args sys -> code : args~List String, sys~System, code~ExitCode
```

The runtime calls it with the command-line arguments and the **root capability**, `System`; its result is the exit code. Types left out of `main`'s signature are these, and types written must be these (E0366), except that the result may also be a `Future ExitCode` ([Concurrency](concurrency.md#ending-the-program)). `main` may be `partial`.

```checkers
module hello

import std.system (System, ExitCode)
import std.terminal

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    terminal.print_line "hello" sys.term
    Success
```

`System` (in `std.system`) is a record of the authorities:

| Field | Type | Authority over |
|---|---|---|
| `term` | `Term` | standard input, output and error |
| `fs` | `Fs` | the file system |
| `env` | `Env` | environment variables, the program's own path |
| `proc` | `Proc` | starting and stopping processes |
| `net` | `Net` | the network |
| `clock` | `Clock` | time |
| `sched` | `Sched` | creating cowns and scheduling behaviours ([Concurrency](concurrency.md)) |

A program takes what it needs with a record pattern, `let System { fs, term } = sys`, or a field, `sys.fs`, and passes on only what each function needs. `ExitCode` is `Success` (exit status 0) or `Failure n`, with `n~U8, n > 0`.

## Authority capabilities

An authority may be used any number of times, and dropped. An operation on it returns only its result:

```checkers
import std.files (Fs, IoError)
import std.files

fn both a b fs -> r : a~String, b~String, fs~Fs, r~Result (Bytes, Bytes) IoError
    let x = try files.read a fs
    let y = try files.read b fs
    Ok (x, y)
```

Two uses of one authority are independent to the prover: the compiler gives each use a token of its own, so no two calls receive the same argument and neither can be proved equal to the other. When the program runs, the calls happen in program order. The cost is that nothing can be proved about the order of effects through an authority (that a read after a write returns what was written).

**Attenuation.** An authority can be narrowed: `files.within dir fs` is an `Fs` that reaches only `dir` (absolute paths and `..` are refused, and so is a symbolic link that leads out of it). Passing a narrowed capability bounds what a function can do.

**Calls for their effect.** A call that returns `Unit` may stand alone as a line of a block, as `terminal.print_line` does above ([Blocks](expressions.md#blocks)).

## Resources

A **resource** is an open, stateful thing that must be released: an open `File` (a file, a pipe, or a standard stream), or a `Child` process. A resource has multiplicity 1: every variable that holds one must be used exactly once on every path that finishes. So forgetting to close a file, or to wait for a child, is a compile error.

A type is a resource if it is one of these, or holds one: a tuple, record or enum with a field of a resource type (`(Option String, File)`, `Result File IoError`), or a `Future` of one. `Option Int` is not a resource, `Option File` is.

```checkers,compile_fail,E0401
import std.files (Fs, File)
import std.files

fn leak path fs -> r : path~String, fs~Fs, r~Bool
    match files.open path fs
        Ok f  -> True
        Err _ -> False
```

The rules, each with its error:

| Rule | Error |
|---|---|
| used exactly once: not zero times, not twice | E0401 |
| used on every path, or on none (an `if` that closes a file in one branch only) | E0402 |
| never dropped by `_`, or by a field left out of a record pattern | E0404 |
| used by a closure only if the closure is called exactly once ([One-shot closures](#one-shot-closures)) | E0401 |
| not put in a cown | E0405 |
| a field of a value holding a resource isn't read with `.f` if another field holds one: that would drop it (take it apart with `match`) | E0406 |
| an array of resources isn't indexed: that would drop the other elements (use a `List`, taken apart with `match`) | E0407 |
| not used in a `match` guard, which runs before the arm's body | E0408 |

A `try` that returns early ([Expressions](expressions.md#try)) is a path like any other: a resource in scope must already be used there. Specifications and proofs may mention resources freely; they use nothing.

### Threading a resource

An operation on a resource consumes it and returns a fresh one with its result, `(result, resource)`, the resource last. A `let` takes the pair apart, binding the result and rebinding the resource under its old name:

```checkers
import std.files (File, IoError)
import std.files

# The first line of a file and the file closed.
fn first_line f -> r : f~File, r~Result (Option Bytes) IoError
    let (line, f) = files.read_line f
    let _ = files.close f
    line
```

The new `f` hides the one used up by the call, so the old one can't be used again. Because each operation consumes the resource the last one returned, the operations are in sequence for the prover too. An operation on an authority returns only its result: `let (x, fs) = files.read path fs` is a type error (E0201).

### One-shot closures

A closure (a lambda, or a function applied to some of its arguments) that uses a resource holds it, so it must be called exactly once, or the resource would be used twice or never. Such a closure may be:

- called where it is made: `(\_ -> files.close f) ()`;
- bound with `let` and called once: the variable is then used exactly once, like a resource;
- passed to a parameter declared `own` on a function type, `k~own (Unit -> a)`, which promises a single call ([Types](types.md#own)).

Anywhere else (passed to a parameter that isn't `own`, returned, called twice or never) is E0401. The function given to `future.fork` is one-shot, so work scheduled with it can take a resource along ([Concurrency](concurrency.md#futures)).

```checkers
import std.files (File, IoError)
import std.files

fn run k -> r : k~own (Unit -> a), r~a
    k ()

fn close_later f -> r : f~File, r~Result Unit IoError
    run (\_ -> files.close f)
```

```checkers,compile_fail,E0401
import std.files (File, IoError)
import std.files

fn many k -> r : k~(Unit -> a), r~a
    k ()

fn close_twice f -> r : f~File, r~Result Unit IoError
    many (\_ -> files.close f)
```

### Generic code and `own`

A generic function might copy or drop a value of its type parameter, so it may be given a resource only through a parameter declared `own`: `v~own a` is used exactly once ([Types](types.md#own)). Functions that could drop elements, such as taking part of a list, can't be called on a list of resources.

```checkers
fn keep x -> r : x~own a, r~a
    x
```

## Files and streams

`std.files` and `std.terminal` give every byte stream as a `File`: a file opened with `files.open` or `files.create`, the standard streams (`terminal.stdin term`, `stdout`, `stderr`), and the pipes of a child process. The same operations read and write all of them, each returning the `File` again:

| Operation | Gives |
|---|---|
| `files.read_line f` | the next line's bytes without its `\n`: `Ok None` only at the end, and an error if reading fails |
| `files.read_some n f` | at most `n` bytes, at least one unless at the end |
| `files.read_exactly n f` | `n` bytes, fewer only at the end |
| `files.read_rest f` | everything to the end |
| `files.write_line s f`, `files.write_bytes b f` | writes |
| `files.flush f` | writes out what is buffered |
| `files.close f` | consumes the file; one open for writing has what is buffered written out first, and an error doing that or closing it is the result |

`files.read path fs` and `files.write path bytes fs` read or write a whole file in one call, without a resource. `terminal.print_line`, `eprint_line`, `write` and `read_line` are shorthands on `Term`.

## Processes

`std.proc` runs other programs with a `Proc`:

- `proc.exec program args p` runs a program with this program's standard streams and gives its exit code.
- `proc.run program args input p` gives it `input` on standard input and gives its exit code and everything it wrote, as an `Output`.
- `proc.spawn program args streams p` starts it and gives a `Spawned streams`: the `Child`, and for each of its three streams declared `Pipe` a `File` for this program's end. The types of those fields are computed from `streams` (`pipe_end Pipe` is `File`, any other is `Unit`), so a program gets a file exactly for each stream it piped, and must close each.
- `proc.wait child` consumes the `Child` and gives its exit code. `proc.killer child` gives a `Killer`, an ordinary value that can end the child from elsewhere.

```checkers,no_run
import std.proc (Spawned, Streams, Pipe, Inherit, Discard)
import std.proc
import std.system (Proc)
import std.files (IoError)
import std.files

fn listing p -> r : p~Proc, r~Result Bytes IoError
    match proc.spawn "ls" [] (Streams Discard Pipe Inherit) p
        Ok (Spawned child () out ()) ->
            let (text, out) = files.read_rest out
            let _ = files.close out
            let _ = proc.wait child
            text
        Err e                        -> Err e
```
