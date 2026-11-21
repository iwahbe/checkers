# Running programs

`checkers run FILE.ck ARGS…` checks a program, compiles it to native code in memory, and runs its `main` with the arguments after the file name. `checkers build FILE.ck -o PROGRAM` writes an executable instead. A program with any error is neither run nor built (exit status 2), unless the only errors are unproven obligations and it is run with `--unverified` (below).

## Erasure

Before a program runs, it is staged ([Staging](staging.md)) and then **erased**: types, type arguments, `ghost` parameters and fields, predicates, lemmas, `have`s and proofs are removed. What remains is a functional program over numbers, strings, arrays, constructors, tuples, closures and capabilities. Proofs therefore cost nothing at run time, and a refinement such as `U8` is not checked when the program runs: it was proved.

## Evaluation

- Evaluation is strict: a call evaluates its arguments, left to right, then the body.
- A block runs its lines in order, so effects happen in the order the program writes them.
- `and`, `or`, `implies`, `if` and `match` evaluate only what they need.
- `Int` and `Nat` have no limit: a result that doesn't fit a machine word becomes a larger number, never a wrong one. `/` and `%` are Euclidean.
- A call in tail position doesn't grow the stack, so a loop written as tail recursion runs in constant space. Other recursion may go deep: each behaviour, `main` included, has a stack of 256 MiB, used only as needed.
- Memory is managed by reference counting, with no pauses for collection. Since values are immutable they can't form cycles; a value that isn't shared may be reused in place when a new one of the same shape is built from it.

## Showing values

`std.string` shows values as text in two ways, through two classes:

- **`display x os`** (the class `Display`) shows `x` to a user, with options of its type's own. Only the types that have an instance can be shown so; a program writes `instance Display T` for its own types, in the module that declares `T`. **`format`** is a template's tag built on it: each hole is shown with `display`, with the options after `|`.
- **`debug x`** (the class `Debug`) writes `x` as Checkers source, for tests and diagnostics. Every type has it.

```checkers
import std.string (format, display, debug, Hex, Digits, Quoted)

check format"{1 + 2} is {"three"}" == "3 is three"
check format"{255 | Hex, Digits 4}" == "0x00ff"
check display "hi" [Quoted] == "\"hi\""
check debug (Some "hi") == "Some \"hi\""
```

`format` is a template's tag, not a function of a value: `format x` is an error (E0293). The standard library's instances of `Display`:

| Type | Options | Shown |
|---|---|---|
| `Int` (so `Nat`, `Char` and the fixed-width numbers) | `IntOption`: `Hex`, `Binary`, `Octal` (with `0x`, `0b`, `0o`), `Plus` (a `+` before a number that isn't negative), `Digits n` (at least `n` digits, zeros before them) | in decimal |
| `String` | `StringOption`: `Quoted` (as `debug` shows it), `Take n` (the first `n` characters) | itself |
| `Bool` | none | `True`, `False` |
| `Decimal` (`std.decimal`) | `DecimalOption`: `Plus`, `Places n` (rounded half away from zero to `n` digits after the point) | as `decimal.render` writes it |

Where two options conflict, the later one wins. Containers (`List`, `Option`, tuples, …) and `()` have no `Display`: show their parts, or use `debug`.

`debug` writes a value the way it would be written in source. A type's own module may replace this with `instance Debug T`; it is then used wherever a `T` is shown, inside other values too:

| Value | Written |
|---|---|
| a number | in decimal: `-5`, `97` (a `Char` or a byte is a number) |
| a `String` | quoted, with escapes: `"a\n"` |
| `Bytes` | `b"…"` |
| a constructor | its name and fields: `True`, `Some (Ok 1)`, `Point 1 2` |
| a list, an array | `[1, 2]` |
| a tuple, `()` | `(1, "a")`, `()` |
| a function, a capability | `<function>`, `<Fs>`, … |

```checkers
import std.string (debug)

check debug (Some (Ok 1)) == "Some (Ok 1)"
check debug (1, "a") == "(1, \"a\")"
check debug "hi" == "\"hi\""
check debug b"hi" == "b\"hi\""
```

A failed `check` shows its values in this derived form, whatever a type's own `Debug` says, so that two different values never look the same there.

## Run-time checks

Every obligation is proved before a program runs, so in a program that checks without errors no operation can fail. `checkers run --unverified` runs a program whose only errors are unproven obligations (E0450, E0451, E0240), for trying out code whose proofs aren't finished. Then the operations that guard against a bad value are checked as the program runs:

| Operation | Checked |
|---|---|
| `a - b` on `Nat`s | `a >= b` |
| `a / b`, `a % b` | `b != 0` |
| `a[i]` | `i < len a` |
| a `match` reaching a case its arms leave out | always fails |
| `main` returning `Failure n` | `1 <= n <= 255` |

A failed check stops the program with a message naming the operation and the function, and exit status 70:

```text
runtime error in `pick`: index 5 out of bounds for 2 bytes
```

Other conditions (a postcondition, a value staying within `U8`) aren't checked at run time.

## Exit status

| Status | When |
|---|---|
| 0 | `main` returned `Success` |
| `n` | `main` returned `Failure n` |
| 2 | `checkers run` found errors, and didn't run the program |
| 70 | a run-time check failed |

If `main` returns a `Future ExitCode`, the status is the future's value, once every behaviour has finished ([Concurrency](concurrency.md#ending-the-program)).

## Release builds

`checkers build --release` refuses a program that relies, anywhere in what it loads, on an `admit` (E0455): an assumption no one proved ([Proofs](proofs.md#the-trust-ledger)). It can't be combined with `--unverified`.
