# Staging

Part of a program can run while it is compiled. A parameter declared `comptime` must be known when compiling, and a function with one is **expanded** at each call: the code that depends only on compile-time values runs then, choosing branches and unrolling recursion, and what is left is ordinary run-time code. A format string, a table, a parser's grammar can be turned into code this way, with no interpretation left at run time.

## `comptime` parameters

```text
constraint ::= lname '~' 'comptime' type
```

```checkers
# `n` is known when compiling; `x` is not.
fn power n x -> y : n~comptime Nat, x~Int, y~Int
    decreasing n
    if n == 0 then 1 else x * power (n - 1) x

fn cube x -> y : x~Int, y~Int
    power 3 x               # compiled as x * (x * (x * 1))

check cube 2 == 8
```

Every call must give a `comptime` parameter a value known when compiling: a literal, a constant, another `comptime` parameter, or the result of code run at compile time. An argument that depends on a run-time value is E0270.

Inside the function, an `if` or `match` on compile-time values picks its branch while compiling, and recursion on them unrolls. Everything else becomes run-time code, with each run-time argument evaluated once, in order.

**What can be known at compile time:** pure values: numbers, `Bool`, `Char`, `String`, `Bytes`, enums, records, lists and tuples of these, types, and functions. Compile time has no capabilities, so it can't read files, the clock or the environment.

## Restrictions

- A function with a `comptime` parameter is expanded where it is called, so it must be called with all its arguments: passing it as a value, or applying it partly, is E0271. Wrap the call in a lambda (`\x -> power 3 x`).
- A `partial` function or a lemma can't have `comptime` parameters (E0272): staging must finish, so compile-time recursion follows the usual termination rules ([Termination](termination.md)).
- If code that staging needs to run stops with a run-time error (a division by zero in a compile-time value), the call is E0273. A failure in code whose value staging doesn't need is left for run time.

## Proofs

A function with `comptime` parameters is proved once, with those parameters unknown, so its proofs hold for every value it is expanded with; the expanded code isn't proved again.

## Types computed at compile time

A `comptime` argument may decide the type of the call. Here `fmt`'s format string decides how many arguments it takes, and of which types: `fmt "{} is {n}"` is a `String -> Int -> String`.

```checkers
enum Piece
    Text s : s~String
    Str
    Num

fn format_type ps -> t : ps~List Piece, t~Type
    match ps
        []             -> String
        Text _ :: rest -> format_type rest
        Str :: rest    -> String -> format_type rest
        Num :: rest    -> Int -> format_type rest

fn go ps acc -> f : ps~comptime List Piece, acc~String, f~format_type ps
    match ps
        []             -> acc
        Text t :: rest -> go rest (acc ++ t)
        Str :: rest    -> \x -> go rest (acc ++ x)
        Num :: rest    -> \n -> go rest (acc ++ format n)

fn greet name age -> s : name~String, age~Int, s~String
    go [Str, Text " is ", Num, Text " years old"] "" name age

check greet "Ada" 36 == "Ada is 36 years old"
```

The type checker computes such types by evaluating the functions in them, so those functions must be visible where the type is used: in the same module, or exported `transparent` ([Modules](modules.md#sealing)). The standard library's `string.bytes` and `utf8.encode` compute on literals there.

## Expansion

A call of a function with `comptime` parameters is expanded in place. When the expansion reaches a call of the same function with the same compile-time arguments (a recursion on run-time values), that becomes one run-time function for those arguments, called from both places. Compile-time arguments that change at every step would need unboundedly many such functions, and are E0273.

`checkers stage FILE.ck` prints each function as staging leaves it, for seeing what was expanded.
