# Modules and packages

## Modules

A file is a module. It starts with a `module` line naming it, then its imports, then its declarations:

```text
file   ::= 'module' qname NL { import NL } { decl }
qname  ::= lname { '.' lname }
```

```checkers
module geometry.area

import std.list

export fn total xs -> n : xs~List Nat, n~Nat
    sum xs

fn sum xs -> n : xs~List Nat, n~Nat
    match xs
        []        -> 0
        x :: rest -> x + sum rest

check total [1, 2, 3] == list.length [0, 0, 0, 0, 0, 0]
```

A file without a `module` line is error E0101; an import after a declaration is E0103. A module name is lowercase, its parts separated by `.`. Inside a program, the module `a.b` is the file `a/b.ck` below the program's root directory, and that file must declare `module a.b` (E0223). The root is the directory the module names are relative to: for the file `tools/ck/syntax.ck` declaring `module ck.syntax`, it is `tools/`.

## Imports

```text
import ::= 'import' qname [ '(' name { ',' name } ')' ] [ 'as' lname ]
```

An import makes a module's exported names available through a **qualifier**, by default the last part of the module's name; `as` chooses another. A list in parentheses also brings those names in unqualified.

```checkers
import std.list                 # list.map, list.length
import std.string as str        # str.concat
import std.files (Fs, IoError)  # files.read; Fs and IoError unqualified

fn count xs -> n : xs~List String, n~Nat
    list.length xs

check str.concat ["a", "b"] == "ab"
```

**Where a module comes from** is decided by the first part of its name:

1. `std`: the standard library (`import std.list`);
2. the name of a dependency of the package ([Packages](#packages)): that package's module;
3. otherwise a module of this program or package, from its file.

An unknown standard-library module is E0220; a package that isn't a declared dependency is E0227; a module that imports itself, directly or through others, is E0222. Two imports with the same qualifier are E0226; give one of them `as`.

**Importing a type imports its constructors**: `import std.system (ExitCode)` makes `Success` and `Failure` available unqualified. A record's fields are always reached with `.field`, so they are never imported.

**The prelude** is imported into every module without being named: `Int`, `Nat`, `Bool`, `String`, `List`, `Option`, `Result`, the classes `Ord` and `Functor`, and the rest listed in [Types](types.md#the-prelude) and [Classes](classes.md#the-prelude-s-classes).

**Resolving a name.** An unqualified name is looked up in the enclosing scopes (parameters, `let`s, pattern variables), then among the module's own declarations, then among the names its imports bring in unqualified, then in the prelude. A module's own declaration may have the same name as an imported one, and then hides it. A qualified name `q.n` names the export `n` of the module imported as `q`; asking for one it doesn't export is E0206, and naming in an import list one it doesn't export is E0221. Both say so when the module declares the name without exporting it.

## Exports

A declaration is visible outside its module only if it is exported:

```text
decl ::= [ 'export' [ 'abstract' | 'transparent' ] ] decl_body | check | instance
```

What an importer sees depends on the declaration:

| Declaration | Visible to importers |
|---|---|
| `export fn` | its name and signature: parameters, types, preconditions and postconditions |
| `export transparent fn` | its signature and its body |
| `export enum`, `export record` | the type, its constructors, fields and invariants |
| `export abstract enum`, `export abstract record` | the type's name and parameters only |
| `export type` (an alias), `export let` (a constant) | its definition |
| `export lemma` | its statement, not its proof |
| `export class` | the class and its members |
| `instance` | an instance is never exported (E0120): it is in effect wherever its module is loaded ([Classes](classes.md#coherence)) |

`abstract` applies only to `enum` and `record` (E0104), and `transparent` only to `fn` (E0105).

### Sealing

An exported function's body is **sealed**: outside its module, the function is known only by its signature. Type checking never looks inside it, and the prover treats it as an unknown function about which it knows only the postconditions ([Proofs](proofs.md#what-the-prover-knows)). So a library has to export, as postconditions and lemmas, every fact its users need: a sort exports that its result is sorted and a permutation, not its algorithm.

```checkers
module counting

export fn three -> n : n~Nat, n == 3
    3

export fn four -> n : n~Nat
    4
```

```checkers,compile_fail,E0450
module uses_counting

import counting

# `three`'s postcondition says what it returns; `four`'s says nothing, so
# the second lemma can't be proved here.
lemma three_is_three
    ensures counting.three == 3

lemma four_is_four
    ensures counting.four == 4
```

`export transparent` unseals a function: its body is visible to type checking and to the prover everywhere, and so is every private function it calls. Its body becomes part of the module's interface. It is meant for small definitions that specifications are written in terms of, and for functions that compute types ([Staging](staging.md)).

Type aliases and constants are always transparent: they are part of the types.

### Abstract types

An abstract type's constructors and fields are private to its module: another module can't build a value of it, match on it, or read its fields (E0247). Only the functions its module exports can. This is how a module keeps an invariant that no constructor states, or decides every way a value is made and used.

```checkers
module token

export abstract record Token
    id~Nat

export fn first -> t : t~Token
    Token 0

export fn next t -> u : t~Token, u~Token
    Token (t.id + 1)
```

```checkers,compile_fail,E0247
module forge

import token (Token)

fn fake -> t : t~Token
    Token 42
```

**Polarity.** Because importers can't see an abstract type's fields, they can't tell how it uses its type parameters. Its declaration states it, with a mark on each parameter:

- `+a`: `a` occurs only in positive places (never to the left of a `->`). The type is covariant in `a` and may hold the type being defined, so `Json` can contain a `Map String Json`.
- `-a`: `a` occurs only in negative places. The type is contravariant in `a`.
- no mark: no promise; the type is invariant in `a`.

The module checks each mark against the fields (E0359). Marks are allowed only on abstract types (E0360): any other type's variance is worked out from its constructors. Variance decides when a value with a refined type argument may be used at a weaker one ([Types](types.md#refinements-inside-types)).

```checkers
module boxes

export abstract record Box +a
    item~a

export fn wrap x -> b : x~a, b~Box a
    Box x
```

## Packages

A package is a directory with a manifest, `checkers.json`, and its modules: the file `a/b.ck` in it is the module `a.b`.

```json
{
  "name": "parser_tools",
  "version": "0.3.1",
  "toolchain": "0.1.0",
  "dependencies": {
    "json_schema": { "git": "https://github.com/example/json_schema", "version": "1.2.0" },
    "shared": { "path": "../shared" }
  }
}
```

| Field | Required | Meaning |
|---|---|---|
| `name` | yes | lowercase letters, digits and `_`, starting with a letter; not `std` |
| `version` | yes | `MAJOR.MINOR.PATCH` |
| `toolchain` | yes | the oldest version of the compiler this package works with |
| `dependencies` | no | each name maps to a git repository and the oldest version that works (a tag `vMAJOR.MINOR.PATCH`), or to a directory relative to this manifest |

An unknown field, a missing required one or a malformed value is an error at its line and column in the manifest. A dependency's name must be the `name` in its own manifest.

**Names.** A package's own modules are named, declared and imported by their path in the package (`module validate`, `import validate`). Another package imports them with the package's name first: `import json_schema.validate`, used as `validate.check`.

**Versions.** The build uses, for each dependency, the highest of the versions that the packages in the build ask for (minimal version selection, as in Go): a release upstream changes nothing until a manifest asks for it. Two major versions of one package in one build are an error. `checkers.lock`, written by the build tool, records each dependency's exact commit, so a build is reproducible.

**Checking.** A dependency's proofs are checked with the program, like the program's own; there is no way to use a dependency unchecked. A dependency runs no code while the program is built (there are no build scripts, and compile-time code is pure, [Staging](staging.md)), and it has no effects at run time except through the capabilities its callers pass it ([Capabilities](effects.md)).
