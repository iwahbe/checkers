# Checkers — Language Specification

**Version:** 0.1 (draft) · **Last updated:** 11/05/2026 (rev. 2) · **File extension:** `.ck`

This document is the single source of truth for Checkers. Implementation follows the spec, never the other way around. Items marked **(proposed)** are Claude's recommendations awaiting Ian's veto; everything else is decided.

---

## 0. Decision log

| ID | Decision | Date | Status |
|----|----------|------|--------|
| D0 | Pillars: compile-time execution; dependent types + built-in prover; sealed module interfaces; functional + immutable; actors own concurrency & resources; interpreter first, Cranelift later; minimal Python/Haskell-ish syntax; types written only as constraints. | 11/05/2026 | decided |
| D1 | **Trust the SMT solver (Z3).** SMT-discharged obligations are accepted without certificate re-checking. Every use is recorded in a per-module *trust ledger* (§7.4) so certificate checking can be added later without changing the language. | 11/05/2026 | decided |
| D2 | Core calculus is **Quantitative Type Theory** with multiplicities {0, 1, ω} (Atkey 2018; as implemented in Idris 2). | 11/05/2026 | decided (11/06/2026) |
| D3 | `Prop` is a definitionally proof-irrelevant, impredicative universe (as in Lean 4). | 11/05/2026 | **(proposed)** |
| D4 | **Pattern matching is checked as case trees** (as in Agda and Idris 2): the elaborator compiles `match` to case trees over constructors and literals, checks exhaustiveness, and checks structural recursion on them. *Revises the 11/05/2026 recursors-only proposal*, which would need dependent pattern-match compilation to eliminators before anything runs; recursors can return later as a proof certificate. | 11/05/2026 (rev.) | decided (11/05/2026) |
| D5 | Implementation language: Rust (Cranelift and the `z3` bindings are Rust-native). | 11/05/2026 | decided (11/06/2026) |
| D6 | `Int` and `Nat` are arbitrary-precision (match SMT `Int` exactly). Fixed-width types are **refinements**, not separate number systems: `U8 = n~Nat, n < 256`, `I64 = n~Int, -2^63 <= n, n < 2^63`. Overflow is therefore a proof obligation, never a silent wrap; wrapping arithmetic is explicit (`wrapping_add`, …). `-` on `Nat` requires `a >= b`. The backend stores refined numbers in machine words. | 11/05/2026 (rev.) | decided (11/06/2026) |
| D7 | Compile-time staging uses Two-Level Type Theory (Kovács 2022), added in milestone M6, not in the v0.1 core. | 11/05/2026 | decided (11/06/2026) |
| D8 | **Haskell-style application.** Application is juxtaposition (`format x`, `List Int`, `Some b`) and every function is curried (`f x y == (f x) y`; partial application is ordinary). Operators are functions: `(+) 1 2 == 1 + 2`, with sections `(+ 1)` and `(1 +)`. `$` (lowest precedence, right-assoc.) and `.` (composition) behave as in Haskell. Declarations and applications now look the same. *Supersedes the 11/05/2026 parenthesized-call proposal.* | 11/05/2026 (rev.) | decided |
| D9 | **Constraint lists are the only place types are written:** function headers, constructor arguments, record fields, and refinement aliases all use `name~Type, predicate, ...` (§9.3). | 11/05/2026 | decided (11/06/2026) |
| D10 | **Generics by auto-binding:** a lowercase name that appears free in a constraint and is not in scope becomes an implicit, erased (multiplicity 0) parameter. `fn map f xs -> ys : f~(a -> b), xs~List a` is generic in `a`, `b`. | 11/05/2026 | decided (11/05/2026) |
| D11 | **Constructor and field invariants:** predicates in a constructor's or field's constraint list are part of the type. Building the value requires discharging them; matching on it provides them as hypotheses. | 11/05/2026 | decided (11/06/2026) |
| D12 | **Refinement reflection inside a module:** total functions are reflected into the SMT logic (their definitions unfold on demand, Proof by Logical Evaluation). Outside the module only exported signatures, postconditions, and lemmas are visible (sealing, §6), unless exported `transparent`. | 11/05/2026 | decided (11/06/2026) |
| D13 | **Proofs are code:** `lemma … ensures … proof`. In a proof, `match` is case analysis, a recursive lemma call is the induction hypothesis, `have L(args)` adds L's conclusion as a fact, `auto` hands the goal to the pipeline, `admit` skips (recorded in the trust ledger). A proof block (or match arm in one) may end with `have …`; the goal is then closed by an implicit `auto`. No separate tactic language in v0.1. | 11/05/2026 | decided (11/06/2026) |
| D14 | `try e` propagates `Err`/`None` early, on `Result` and `Option`. A prefix keyword (extending to the end of the expression, like `$`) replaces the earlier postfix `e?`, which reads wrongly under juxtaposition: `f x?` would mean `f (x?)`. | 11/05/2026 (rev.) | decided (11/06/2026) |
| D15 | **Interfaces** (type classes, Lean-style instance resolution) provide `==`, `<`, `+`, `format`, etc. Needed for D0's own example (`format x + y`). Detailed design deferred to its own section; until then the prelude's operators are built in. | 11/05/2026 | **(proposed, open)** |
| D16 | **Abstract type constructors declare parameter polarity** (`export abstract record Map k +v`). `+v`: `v` occurs only strictly positively (never to the left of an `->`), so the type is covariant in `v` and may hold the type being defined (a `Json` containing `Map String Json`). `-v`: `v` occurs only negatively, so the type is contravariant in `v`. Unmarked: no promise, so invariant, and a recursive type may not occur there. The defining module checks each mark against the constructors (E0359); importers rely on the marks, for strict positivity and for variance (D71). Marks are only for abstract types (E0360): other types' polarity is worked out from their constructors, where a parameter counts as positive only if it is strictly positive. In the standard library, `Future +a`; `Cown a` is unmarked, so invariant. | 11/05/2026 (rev. 11/06/2026) | decided (11/06/2026) |
| D17 | `match` is first-match. Each arm sees the negations of earlier arms' patterns and guards as hypotheses. | 11/05/2026 | decided (11/06/2026) |
| D18 | `==` inside constraints, `ensures`, and `check` is propositional equality and works on any type. In runtime code, `==` requires an `Eq` instance (D15), derived automatically for enums and records whose fields have one. | 11/05/2026 | **(proposed)** |
| D19 | **Literals.** `'x'` is a **byte** literal (`U8`): one ASCII character or an escape (`'\n'`, `'\\'`, `'\''`, `'\xff'`). `"…"` is a `String` literal; `"'"` is a one-character string. `b"…"` is a `Bytes` literal. Character (`Char`) literals are written `c'é'`. | 11/05/2026 | decided |
| D20 | **`String` is UTF-8**: an immutable byte sequence that is valid UTF-8 by construction (an invariant, D11). `Char` is a Unicode scalar value. | 11/05/2026 | decided |
| D21 | **Naming conventions, enforced by warnings:** keywords are lowercase; types, type constructors, and data constructors are `UpperCamelCase` (`Int`, `List`, `Json`, `Some`); top-level constants are `SCREAMING_SNAKE_CASE` (`MAX_DEPTH`); functions, variables, parameters, fields, modules, and type variables are `lower_snake_case`. Violations are warnings, not errors (codes W001–W005, §9.7). | 11/05/2026 | decided |
| D22 | **Spacing distinguishes `.` and `[`.** Glued (`v.stop`, `list.keys`, `src[i]`): field access, qualified name, indexing. Spaced (`f . g`, `f [x]`): composition, list-literal argument. Same rule as Haskell's `OverloadedRecordDot`. Field access and indexing bind tighter than application, so `Str s.value` is `Str (s.value)`. | 11/05/2026 | decided (11/06/2026) |
| D23 | **Layout = Python-style logical lines** (§9.1): a newline ends a statement unless inside brackets, after a trailing `,` or binary operator, or before a line that starts with a binary operator or `:`. An indented block may follow any line that ends a header (`fn`, `enum`, `record`, `lemma`, `match`, an `if`/`else` line, a match arm ending in `->`, `proof`, `let x =`). | 11/05/2026 | decided (11/06/2026) |
| D26 | **Two namespaces for `Uname`s, chosen by position.** After `~` in a constraint (and in a `type` alias's first constraint) a `Uname` resolves to a type; elsewhere it resolves to a data constructor or constant. So `enum Json` may have a constructor `Bool b : b~Bool`, and `record Error` is built with `Error pos kind` while its type is `Error src`. `lname`s share one namespace everywhere, so values used inside types (`Parsed Json src i`) work. This is Haskell's split, made sound for dependent types by D9 (types only ever appear after `~`). | 11/05/2026 | decided (11/06/2026) |
| D27 | **Effects go through capabilities** (§8.1–8.2). Every effectful operation takes a capability; the kernel treats capabilities as linear, so every function stays a mathematical function. `main` receives `sys~System`, a record of authority capabilities (`term`, `fs`, `env`, `proc`, `net`, `clock`, `sched`). No `IO` monad and no effect system in the kernel. | 11/05/2026 | decided |
| D28 | **Authority is copied on use; resources are linear** (§8.1, §8.3–8.4). Authority capabilities (`System`, `Term`, `Fs`, `Env`, `Proc`, `Net`, `Clock`, `Sched`) may be used any number of times and dropped: the elaborator gives each use a fresh token, so the kernel still sees exact linearity. Cost: no proven ordering between uses of one authority, and closures capturing one are single-use. Resources (`File`, `Child`, `Pipe`, `Socket`) are `own`, used exactly once, and closed explicitly. *Supersedes the 11/05/2026 droppable-but-linear proposal and `files.split`.* | 11/05/2026 | decided |
| D29 | **`x <- f a r`** means `let (x, r) = f a r`, where the last argument `r` is a **resource** variable (§8.4). `<-` also binds the future returned by `fork`/`join` (§8.6). | 11/05/2026 | decided (11/06/2026) |
| D30 | **Concurrency is cowns + `when`** (behaviour-oriented concurrency, Verona; §8.5): race- and deadlock-free by construction, causal order, invariants as refinement types on contents. Actors and channels are libraries on top. *Supersedes the actors-with-session-types plan for M7.* | 11/05/2026 | decided (syntax decided 11/05/2026) |
| D31 | `main`'s signature: `fn main args sys -> code : args~List String, sys~System, code~ExitCode` (it may be `partial`). `code` may also be a `Future ExitCode` (§8.6). The process exits once all scheduled work has finished. | 11/05/2026 | decided (11/06/2026) |
| D33 | **Nothing ever blocks.** No `await`. Effectful fork/join is `f <- fork using sched` and `r <- join x = f, … using sched`: both schedule a behaviour and return a `Future`; a join runs after the forks it names, by causal order (§8.6). | 11/05/2026 | decided (syntax decided 11/05/2026) |
| D34 | **`par (e1, …, en)`** evaluates the components of an n-tuple in parallel and returns the tuple. Pure only; to the prover `par t == t`. A keyword, not a function, because Checkers is strict: a function's arguments would already be evaluated, one after another, before it ran. | 11/05/2026 | decided |
| D32 | **Record patterns** `Ctor { a, b = p }` bind named fields. Fields left out must be authority capabilities or ordinary values; an unmentioned resource field is an error. | 11/05/2026 | decided (11/06/2026) |
| D35 | **`Unit` statements.** A call returning `Unit` may stand alone as a statement line in a block (`terminal.print_line "hi" term`). Any other non-final bare expression is a type error; discard a value with `let _ = …`. | 11/05/2026 | decided (11/06/2026) |
| D36 | **Importing a type imports its constructors**: `import system (ExitCode)` makes `Success` and `Failure` available. Record fields are reached with `.field`. | 11/05/2026 | decided (11/05/2026) |
| D37 | **Inductive types have parameters, not indices.** A family such as `Vec a n` is parameterized by `a` and `n`; constructors relate them with equality constraints (`n == m + 1`), which are refinements (§7). The kernel never unifies indices. | 11/05/2026 | decided (11/05/2026) |
| D38 | **Built-in operators before interfaces (D15).** `+ - * / %` work on `Nat` and `Int`; `< <= > >=` on `Nat` and `Int`; `==`/`!=` on any type; `++` on `String`, `Bytes` and `List a`; `len` on `Bytes`, `String` and `List a`; `format` on any type. Both operands must have the same type; an unconstrained numeric literal defaults to `Nat`. `U8`, `Char` and the other fixed-width types are refinements of `Nat`/`Int` (D6), so they mix freely with them; their ranges are checked by the prover. | 11/05/2026 | decided (11/05/2026) |
| D39 | **Resources are linear by type.** A *primitive resource* is a standard-library type the runtime implements as an open, stateful thing: `files.File` today, `Child`, `Pipe` and `Socket` when they exist. A type is *linear* if it is a primitive resource, or a tuple, record or enum with a linear component or type argument (`(Option String, File)`, `Result File IoError`). `Cown a` and `Future a` are never linear: the cown or future owns its contents, and its handle may be shared (§8.5). A function type whose parameter type is linear takes that argument exactly once (`File -> Unit`). Every variable the program names (parameter, `let`, `<-`, pattern variable) whose type is linear must be used exactly once on every path, whether or not it is written `own`; `own` stays allowed as documentation. A pattern that would drop a resource (`_`, or a field left out of a record pattern) is an error (E0404). | 11/05/2026 | decided (11/05/2026) |
| D40 | **`check e` is run by `checkers check`** (compile-time execution, D0). Native code evaluates `e` (D80; the interpreter until then); `False` is error E0260, a runtime error during evaluation is E0261. Checks receive no capabilities, so they cannot have effects. A check that evaluates to `True` is proven by evaluation; it is still recorded for the prover. | 11/05/2026 | decided (11/05/2026) |
| D41 | **Execution model (§13).** Strict, call-by-value, arguments left to right, block lines in order. Types, `ghost` values, implicit arguments and predicates are erased. Until the prover (M3) discharges obligations, the ones that guard an operation are checked at run time: `-` on `Nat` going below zero, `/` and `%` by zero, `src[i]` out of bounds, an `ExitCode` out of range. A failed check stops the program with a runtime error and exit code 70. Other refinements are not checked at run time. | 11/05/2026 | decided (11/05/2026) |
| D42 | **`format x`** renders a value as Checkers source: `Nat`/`Int` in decimal (`-5`), `Bool` and other constructors by name with arguments (`Counts 1 2 3`, `Some (Ok 1)`), lists `[1, 2]`, tuples `(1, "a")`, `Unit` as `()`, `Bytes` as `b"…"`. A top-level `String` is returned unchanged; strings inside other values are quoted. Functions and capabilities render as `<function>` and `<Fs>` etc. | 11/05/2026 | decided (11/05/2026) |
| D43 | **`checkers run FILE.ck [ARG…]`** type-checks the file (any error stops it, exit code 2), runs its `check`s, then calls its exported `main` with the arguments and the root `System`. The exit code is `0` for `Success` and `n` for `Failure n`. | 11/05/2026 | decided (11/05/2026) |
| D44 | **The M2 scheduler is single-threaded.** `when`, `fork` and `join` append a behaviour to one FIFO queue; after `main` returns, the queue runs until it is empty (behaviours scheduled meanwhile go to the back). FIFO order respects causal order (§8.5) and runs every fork before a join that names it, so it is a valid schedule. `par` evaluates left to right. The multi-threaded scheduler arrives in M7 without changing any program's result. | 11/05/2026 | decided (11/05/2026) |
| D45 | **`own` marks generic parameters that may receive a resource.** `x~own T` means `x` is used exactly once. For a linear `T` this is already implied (D39), so writing it is warning W010. For a `T` with a type variable (`v~own a`) it is what lets a generic function accept a resource: without it, the function might copy or drop `x`, so passing it a resource is an error. On any other type (`n~own Nat`) it is error E0358. Applies to parameters and constructor fields. | 11/05/2026 | decided |
| D46 | **Z3 is linked into the `checkers` binary** (built from source and linked statically), so nothing else needs installing. Queries are still SMT-LIB 2 text, evaluated in-process (`Z3_eval_smtlib2_string`), one solver context per obligation, run in parallel: the query text is what the trust ledger hashes, and `CHECKERS_SMT_DUMP` shows it. Cost: building `checkers` from scratch compiles Z3 (several minutes, once). *Revises the 11/05/2026 subprocess proposal.* | 11/05/2026 | decided |
| D47 | **Permutations are multiset equality.** The prelude-level module `bag` provides `Bag` (a finite multiset of `Int`) with `bag.of xs`, `bag.count x b`; `list.perm xs ys` is `bag.of xs == bag.of ys`. The prover maps `Bag` to Z3 arrays `Int → Int`, so permutation facts are decidable without quantifiers (as Liquid Haskell does with its `Bag` measure). | 11/05/2026 | decided (11/05/2026) |
| D48 | **An obligation the prover can't discharge is an error**: E0450 (Z3 found a counterexample or gave up), E0451 (outside the SMT fragment, §7.3). The message shows the goal, the facts in scope and the counterexample. Examples that need a later milestone are listed in `examples/PENDING` with their expected output under `tests/pending/`; `checkers run --unverified` runs a program whose only errors are unproven obligations, keeping the runtime checks of §13.3. | 11/05/2026 | decided (11/05/2026) |
| D49 | **Proof statements (D13).** `have e`: if `e` applies a lemma, its preconditions become obligations and its `ensures` a fact; otherwise `e` is a `Bool` that is proven, then becomes a fact. `auto` proves the current goal from the facts in scope; `admit` assumes it (trust ledger). `have` may also appear in function bodies. A lemma that uses itself is an induction and must recurse structurally, like a function. | 11/05/2026 | decided (11/05/2026) |
| D50 | **Calls assume the callee's postcondition**, including recursive calls, which is how induction over a function's own recursion works (as in Dafny and Liquid Haskell). This is sound because total functions terminate (structural recursion, or a `decreasing` measure proven to decrease, D55). | 11/05/2026 | decided (11/05/2026) |
| D51 | **A function with a precondition must be called with all its arguments** (E0453): a partial application would hide the call where the precondition is checked. | 11/05/2026 | decided (11/06/2026), relaxed by D52 |
| D52 | **Refined function types are the direction (M10).** A function type may carry predicates over its parameters and result, e.g. `f~(x~Int -> y~Int, x >= 5, y > x)`, with subtyping between refined function types and refined element types (`xs~List (n~Int, n >= 5)`). A partially applied function with a precondition can then be passed wherever the expected function type promises that precondition, and the callee proves it at each call of `f`. Until M10, D51 applies, relaxed: a partial application is allowed when its preconditions mention only the arguments already supplied, and they are checked there. | 11/05/2026 | decided (relaxation of D51 decided 11/06/2026) |
| D53 | **Module files.** `import a.b` loads the standard-library module `a.b` if there is one, else the file `a/b.ck` next to the file being checked (directories mirror dotted names). That file must start with `module a.b` (E0223). Every module a program imports is type-checked, has its `check`s run and its obligations proven, as part of checking the program; errors are reported in the file they belong to. | 11/05/2026 | decided (11/06/2026) |
| D54 | **Sealing is per module (§6).** Outside its module, a function's body is invisible: it never unfolds during type checking, and the prover sees only its signature and postconditions (an uninterpreted function), unless it is exported `transparent`. A transparent function's private helpers (the module-local functions its body calls, transitively) are visible too, to the prover and to type checking, or its body would say nothing; they still can't be named outside. Type aliases and `let` constants stay transparent (they are part of the types). The interpreter always uses the body. | 11/05/2026 | decided (11/06/2026; helper visibility for type checking amended 11/06/2026) |
| D55 | **Termination measures are proof obligations (§5.3).** At every call between functions of one recursive group that use `decreasing`, the callee's measure at the arguments must be lexicographically below the caller's measure at its parameters, under the facts at the call. A recursive use that is not a full call (passing the function as a value) can't be checked and is error E0303. Results of `Nat`-valued functions are known to be `>= 0` at every call that meets the callee's precondition (§7.3). | 11/05/2026 | decided (11/06/2026) |
| D56 | **Axioms about primitives.** In the standard library only, a lemma whose `proof` is `__builtin` states a fact about `__builtin` functions (`decimal.scan_json_render`: scanning a rendered number gives it back). It is trusted like the Rust code it describes. Each use (`have`) is listed in the trust ledger as `axiom`, separately from `admit`s; release builds accept axioms and reject admits. | 11/06/2026 | decided (11/06/2026) |
| D57 | **Known function arguments are seen through (§7.3).** When a function that takes a function is applied to a named function or a lambda with no free variables (`map render items`, `map (\(k, x) -> …) fields`), the prover reflects a copy specialized to that argument. Other function arguments (a lambda using a local) remain outside the fragment (E0451). Lambdas are compared up to the names of their parameters. | 11/06/2026 | decided (11/06/2026) |
| D58 | **Strings are their UTF-8 bytes to the prover (§7.3).** A `String` is translated as its bytes, so `++`, `len` and `utf8.encode` are exact, and `utf8.encode (a ++ b) == utf8.encode a ++ utf8.encode b` is immediate. | 11/06/2026 | decided (11/06/2026) |
| D59 | **`comptime` binders (§8.9).** `x~comptime T` marks a compile-time parameter; every call supplies a compile-time value, and code depending only on such values runs during staging (branches chosen, recursion unrolled). | 11/06/2026 | decided (11/06/2026) |
| D60 | **Stage inference (§8.9).** `quote`/`splice` are inserted by the elaborator (Kovács's coercive subtyping); `Code a`, `quote`, `splice` are written only when building code explicitly. A runtime value never flows to compile time. | 11/06/2026 | decided (11/06/2026) |
| D61 | **Staged functions are proven once (§8.9).** Obligations are proven with `comptime` parameters symbolic; specializations are not re-proven. Compile-time recursion follows §5.3, so staging terminates. | 11/06/2026 | decided (11/06/2026) |
| D62 | **Compile time is pure (§8.9).** Data, types and functions only; no capabilities or effects at compile time. | 11/06/2026 | decided (11/06/2026) |
| D63 | **Dependent `match` (§5.2).** Matching a variable refines the expected type in each arm: the variable is replaced by the arm's constructor. Applied whenever possible; needed for functions whose result type is computed from a parameter (`go` in `examples/format.ck`). | 11/06/2026 | decided (11/06/2026) |
| D64 | **One runtime function per compile-time arguments (§8.9).** An expansion that reaches itself again (same function, same compile-time arguments) becomes a generated runtime function taking the runtime arguments; `checkers stage` prints it as `name[args]`. This is what Zig and C++ templates do, without new syntax; explicit `Code`/`quote`/`splice` (D60) stay for later. | 11/06/2026 | decided (11/06/2026) |
| D65 | **Declarations are checked in dependency order, not file order.** Each declaration may use any other that doesn't depend on it. A declaration's *head* (a type's constructors, a constant's value, a function's or lemma's signature) needs the heads of what it mentions, and the body of a function it mentions in a type or a constant's value (the type or value may have to be computed). Bodies need only heads, so recursion between function bodies is unrestricted. A head that needs itself, through any chain, is E0225 (`A` depends on itself: `A` → `B` → `A`); types may still be mutually recursive. | 11/06/2026 | decided (11/06/2026) |
| D66 | **Multi-threaded scheduling is Verona's algorithm (§13.5).** A behaviour joins the queue of every cown it names in one atomic step and runs when it is first in all of them; behaviours start while `main` runs. Causal order and no deadlock by construction. | 11/06/2026 | decided (11/06/2026) |
| D67 | **`--threads N`** (default: cores). `--threads 1` is the M2 FIFO scheduler, deterministic; golden run tests use it; stress tests use many threads. | 11/06/2026 | decided (11/06/2026) |
| D68 | **Each `terminal` call is atomic**: output from unrelated behaviours may come in any order but never interleaves within a call. | 11/06/2026 | decided (11/06/2026) |
| D69 | **`par` runs its components on the pool.** | 11/06/2026 | decided (11/06/2026) |
| D70 | **Actors are a library** (`stdlib/actor.ck`): a cown of state; `actor.send a f sched` schedules `f` on it. | 11/06/2026 | decided (11/06/2026) |
| D71 | **Refinements inside type arguments are checked (§7.1).** `List Small`, `Option U8` and `Cown Log` mean what they say: every value in that position satisfies the refinement, and the prover already assumes so. (a) **Gaining one is an obligation where a value is built:** a value checked against a refinement alias anywhere gets its predicates as an obligation (a constructor field whose type parameter is instantiated to the alias, as in `n :: xs` against `List Small`; an element of a list literal; the result of a lambda passed to `map`; `Some n` against `Option U8`), as parameters and results already do. (b) **Forgetting one is free:** a `List Small` is also a `List Nat`. This follows the variance of each type argument: covariant for a datatype parameter used only in fields (`List`, `Option`, tuples, records, `Result`, `Parsed`), contravariant for a function's argument, covariant for its result, and for abstract types as their parameters are marked (D16): `Future +a` is covariant, unmarked `Cown a` invariant, so a `Cown Small` is never a `Cown Nat`. (c) **A refinement is never gained through a type argument of an existing value:** passing a `List Nat` where a `List Small` is expected is a type error (E0262); proving it would need a proof about every element, which needs induction. The help line says to give the value the refined type where it is built. **Later:** once the prover supports induction for this, (c) becomes a proof obligation instead of a type error. The obligation is a generated predicate for each type, "every element satisfies the refinement", proven automatically or with lemmas about that predicate (D13, D50). | 11/06/2026 | decided (11/06/2026) |
| D72 | **Native pipeline (§14).** The erased code the interpreter runs is closure-converted into first-order functions and lowered to Cranelift IR. One lowering, two outputs: `checkers run --native` compiles in memory (JIT) and runs, and `checkers build FILE -o PROG` writes an executable (object file linked with the runtime library by the system C compiler). Compile-time evaluation (`check`, D40) and staging (§8.9) stay in the interpreter. | 11/06/2026 | decided (11/06/2026) |
| D73 | **One 64-bit word per value.** Odd words are integers of up to 63 bits; even words point to a heap object (a header with reference count and constructor, then fields). Constructors without fields are words, not objects. Erased values have no representation. `Nat`/`Int` arithmetic is checked: on overflow it continues with a big integer (D6 unchanged). Where a type's refinement bounds a number within 63 bits (`U8`…`U32`, `I8`, `I32`, `Char`), the overflow check is left out. `U64` and `I64` need all 64 bits: they are words while they fit and big integers otherwise, until values are laid out by type (after M8). | 11/06/2026 | decided (11/06/2026) |
| D74 | **Memory: reference counting, Perceus style** (Reinking et al., PLDI 2021). The compiler inserts increments and decrements where values are copied and last used; a value with one reference that is dropped and rebuilt with the same shape is reused in place, which `own` (multiplicity 1) values always allow. Counts are atomic, since values cross threads. No cycle collector: immutable values can't form cycles; a cown that (indirectly) holds itself is never freed. | 11/06/2026 | decided (11/06/2026) |
| D75 | **Tail calls are guaranteed natively too (§13.2).** Every call in tail position uses Cranelift's `tail` calling convention and `return_call`. Deep non-tail recursion runs on threads with 256 MiB stacks, as in the interpreter. | 11/06/2026 | decided (11/06/2026) |
| D76 | **Same behaviour, same tests.** Native code gives the same output as the interpreter, byte for byte, including runtime errors (`runtime error in \`f\`: …`, exit 70) and `format`. Every `tests/run/` and `tests/stress/` case runs both ways against one `.out` file. The runtime (builtins, big integers, the scheduler, I/O) is one Rust library both use where the representation allows. | 11/06/2026 | decided (11/06/2026); superseded by D80 |
| D77 | **The scheduler becomes lock-free in M8** (Verona's per-cown queues with atomic links, Cheeseman et al. 2023, §5), so many small behaviours no longer slow down with more threads (§13.7). After M8, `checkers run` runs native code by default; `--interp` selects the interpreter. | 11/06/2026 | decided (11/06/2026) |
| D78 | **The interpreter stays after M8**, in two roles: the compile-time evaluator (`check`, D40; staging, §8.9), whose values turn back into core terms directly; and the reference that native code is tested against (D76). It stops being a way to run programs except with `--interp`. Every builtin is implemented once in the shared runtime where the representation allows (D76), so the cost of two implementations stays small. | 11/06/2026 | rejected (11/06/2026): see D80 |
| D79 | **Replace M8's third criterion** ("the fork/join tree of §13.7 no slower on 2 threads than on 1"), which compares against the one-thread FIFO queue, where a behaviour costs about 0.3 µs with no synchronisation, while handing a behaviour between cores costs about 1.5 µs. Proposed instead: *the fork/join tree whose leaves each do about 5 µs of work is faster on 2 threads than on 1* (met: 1.35×; 1.6× at 17 µs). Cutting the cost of tiny behaviours further (work stealing with per-worker queues, fewer allocations per behaviour) is left for later. | 11/06/2026 | decided (11/06/2026) |
| D80 | **The interpreter is removed; everything runs as native code** (§14). `checkers run` compiles and runs the program; `checkers check` evaluates `check` declarations (D40) and staging (§8.9) computes compile-time values by compiling them in memory and running them. A compile-time value is turned back into a term from its words (numbers, strings, bytes, constructors, tuples). One implementation: compile-time and run-time evaluation can't differ, each builtin is written once, and slow compile-time work (real proofs, heavy staging) runs at native speed. The cost is a few milliseconds of compiling per file, even when its checks are trivial. A runtime error during compile-time evaluation stops that evaluation only (E0261, E0273), not `checkers`. `--interp` is gone. | 11/06/2026 | decided (11/06/2026) |
| D81 | **No shell in this repository; M9 is removed** (§10). The shell capstone moves out of the project; M10 follows M8. Proofs about effectful protocols use pure state machines in cowns (§8.8): the state's invariant is the cown's content type, transitions are pure verified functions, and behaviours apply them. Separation-logic specifications over capability state are not scheduled. The `env` and `proc` libraries (`Env`, `Proc`, `Child`, `Pipe`, §8.1–8.4) stay specified but are built only when a program needs them. | 11/06/2026 | decided (11/06/2026) |
| D82 | **Refined types can be written inside types (M10, §7.5).** In a type, a parenthesized constraint list is a refinement type: `xs~List (n~Int, n >= 5)`. A function type may name its parameter and result and constrain them: `f~(x~Int -> y~Int, x >= 5, y > x)`, where predicates that mention only parameters are preconditions and the others postconditions. An unnamed side stays plain: `(x~Int -> Int, x >= 5)`. Each is an anonymous refinement alias, so everything D71 says about aliases holds for it. | 11/06/2026 | **(proposed)** |
| D83 | **Weakening a refinement is a proof obligation, not a type error (§7.5).** Where D71 compares a found and an expected refinement in a covariant position (a type argument, a function's result), the found one may be stronger: `List (n~Int, n >= 6)` passes as `List (n~Int, n >= 5)` when the prover shows `n >= 6 ⇒ n >= 5` for any `n`. That is first-order (no induction: it is about one element), so it is an obligation (E0450) with a counterexample. A contravariant position (a function's parameter) flips it. Gaining a refinement where the found type has none (`List Int` as `List Big`) stays E0262 (D71c). Two refinements are compared by implication, not by name: `Big` and `(n~Int, n >= 5)` are the same type. | 11/06/2026 | **(proposed)** |
| D84 | **Calls of function-typed values (§7.5).** Calling `f a` where `f~(x~A -> y~B, P x, Q x y)` obliges `P a` (as D71 already does for an alias parameter) and gives the fact `Q a (f a)`, so the result is known to satisfy the function type's postcondition. The prover keeps `f` uninterpreted (§7.3) and adds the fact at each call. | 11/06/2026 | **(proposed)** |
| D85 | **Passing a function where a refined function type is expected (§7.5).** A named function, a partial application or a lambda passed where `(x~A -> y~B, P x, Q x y)` is expected is checked against it: the expected precondition must imply the function's own (`P x ⇒ pre x`, contravariant), and its own postcondition must imply the expected one (`P x ∧ post x y ⇒ Q x y`). Both are obligations (E0450) at the place it is passed, reported as "`list.map` may call `at_least 7` with any `x` where `x >= 5`, but it needs `x >= 7`", with a counterexample. A lambda's body is checked with `P x` as a fact and `Q x y` as an obligation on its result, as D71 already does for aliases. A function type with no predicates is the weakest expectation: passing a function with a precondition there fails with a counterexample. | 11/06/2026 | **(proposed)** |
| D86 | **Partial applications are allowed everywhere; E0453 is retired (lifts D51).** `at_least 5` has the refined function type `(x~Int -> y~Int, x >= 5)`: the remaining parameters, with the supplied arguments put into the preconditions and postconditions. Where it is passed, D85 checks it; where it is called, D84. So `list.map (at_least 5) xs` checks when every element of `xs` is known to be at least 5. The failure E0453 reported becomes a D85 obligation with a counterexample. E0453 is not reused. | 11/06/2026 | **(proposed)** |
| D87 | **Function arguments are typed before the function is (§7.5).** For a call like `list.map sub5 xs`, the elaborator takes the type of `xs` before checking `sub5` against `(a -> b)` (as it already does for a lambda, D71), so `a` is `Big` and D85 can see the promise `xs` makes. Without this, the order of arguments would decide whether a program checks. | 11/06/2026 | **(proposed)** |
| D24 | **Development loop:** Claude owns the implementation; Ian drives with examples. An issue is "found X, expected Y" with a `.ck` snippet. Each one becomes a regression test under `tests/` *before* the fix lands, and the spec is updated first whenever the expectation changes the language. | 11/05/2026 | decided |
| D25 | **Milestones reordered for CLI tools first** (§10): a running interpreter with `IO` comes right after type checking, before the prover, so Checkers can be used to build its own tooling early. ~~Capstone: an interactive shell with a small scripting language, with proofs of its correctness.~~ (removed by D81) | 11/05/2026 | decided |

---

## 1. Architecture

```
 .ck source
    │ parse
    ▼
 Surface AST ──elaborate──▶ Core terms (QTT)  ◀── kernel checks these; trusted
    │  (constraints → Π/Σ/refinements,          │
    │   implicit args, pattern matching          │ prover obligations ──▶ Z3 (trusted, D1)
    │   → recursors, unification)                ▼
    │                                     Erasure (drop all 0-multiplicity content)
    │                                            ▼
    │                                     Runtime IR ──▶ Cranelift (M8, D80): in memory for `run`,
    │                                                    `check` and staging; executables for `build`
```

Three components are trusted: the **kernel** (core type checker), **Z3**, and the **Rust compiler/runtime**. The elaborator, parser, and optimizer are untrusted: if they produce a wrong core term, the kernel rejects it.

---

## 2. Multiplicities

Every binder carries a multiplicity ρ ∈ {0, 1, ω}:

| ρ | Meaning | Checkers use |
|---|---------|--------------|
| 0 | Erased. May appear only in types and proofs; never exists at runtime. | Proofs, type arguments, ghost values |
| 1 | Linear. Used exactly once at runtime. | Resources (open files, child processes, sockets); capabilities in the kernel (§8.3) |
| ω | Unrestricted. | Ordinary immutable values |

Arithmetic (ordered semiring, as in Idris 2):

```
 +  | 0  1  ω        ·  | 0  1  ω
 ---+---------       ---+---------
 0  | 0  1  ω        0  | 0  0  0
 1  | 1  ω  ω        1  | 0  1  ω
 ω  | ω  ω  ω        ω  | 0  ω  ω
```

Order: 0 ≤ ω and 1 ≤ ω (0 and 1 are incomparable). A variable available at ω may be used as 0 or 1 (sub-usaging); a variable available at 1 may **not** be used as ω.

---

## 3. Core syntax

```
ρ, π ∈ {0, 1, ω}                         multiplicities
ℓ    ∈ ℕ (+ level variables, later)       universe levels

t, A, B ::= x                             variable
          | c                             global constant (definition, inductive, constructor, recursor)
          | Type ℓ                        universe of types
          | Prop                          universe of propositions (D3)
          | (x :π A) → B                  dependent function type
          | λ x. t                        abstraction
          | t u                           application
          | (x :π A) × B                  dependent pair type
          | (t, u)                        pair
          | let (x, y) :ρ = t in u        pair elimination
          | let x :ρ A = t in u           local definition
          | t = u                         propositional equality (in Prop)
          | refl                          equality proof
          | smt_trusted φ                 SMT-discharged proof of φ (§7.4; kernel-visible axiom instance)
```

Inductive families, records, and the integer/string literals are introduced by **declarations** (§5), not term formers.

---

## 4. Typing rules

Contexts: `Γ ::= · | Γ, x :ρ A`. `0Γ` sets every multiplicity in Γ to 0. `Γ₁ + Γ₂` and `πΓ` are pointwise and defined only when `0Γ₁ = 0Γ₂` (same variables and types).

Judgment: `Γ ⊢ t :σ A` with σ ∈ {0, 1}. σ = 1 checks `t` as a runtime term (usage counts); σ = 0 checks it as type-level/erased (usage ignored). The rules are those of Atkey 2018 §2; the essential ones:

```
                    ──────────────────────────────── VAR
                    0Γ, x :σ A, 0Γ' ⊢ x :σ A

  0Γ ⊢ A :0 Type ℓ₁     0Γ, x :0 A ⊢ B :0 Type ℓ₂
  ──────────────────────────────────────────────── PI
       0Γ ⊢ (x :π A) → B :0 Type (max ℓ₁ ℓ₂)

           Γ, x :(σ·π) A ⊢ t :σ B
  ──────────────────────────────────────── LAM
       Γ ⊢ λ x. t :σ (x :π A) → B

  Γ₁ ⊢ f :σ (x :π A) → B     Γ₂ ⊢ a :σ' A     σ' = 0 ⇔ (π = 0 ∨ σ = 0)
  ──────────────────────────────────────────────────────────────────── APP
                Γ₁ + π·Γ₂ ⊢ f a :σ B[a/x]

       Γ ⊢ t :σ A     0Γ ⊢ A ≡ B
  ────────────────────────────────── CONV
            Γ ⊢ t :σ B

       Γ ⊢ t :σ A     Γ ≤ Γ'
  ────────────────────────────── SUB (sub-usaging, pointwise ≤ from §2)
            Γ' ⊢ t :σ A
```

Σ, let, and equality follow the same pattern (Atkey 2018 §2 for Σ/⊗). Universes are cumulative and predicative: `Type ℓ : Type (ℓ+1)`. `Prop : Type 0`, and `Prop` is impredicative: `(x :π A) → P : Prop` whenever `P : Prop`.

**Proof binders are erased automatically:** any binder whose type lives in `Prop` is forced to multiplicity 0. Users never write multiplicities on proofs.

**Erasure theorem (inherited from QTT):** a term checked at σ = 1 can be run with every 0-annotated subterm deleted. This is what makes proofs cost nothing at runtime.

---

## 5. Declarations

### 5.1 Definitions
Order in the file doesn't matter: declarations are checked in dependency order, and a declaration may use any other that doesn't depend on it (D65).
```
def f :ρ A = t              transparent: unfolds during conversion
opaque def f :ρ A = t       opaque: never unfolds outside its own module (§6)
```

### 5.2 Inductive families
Strict positivity is required. Each inductive `D` generates constructors and one recursor `D.rec` (dependent eliminator) with ι-reduction. Example (`Vec`):
```
inductive Vec (A : Type ℓ) : Nat → Type ℓ
  | nil  : Vec A 0
  | cons : (n :0 Nat) → A → Vec A n → Vec A (n + 1)
```

**Dependent `match` (D63).** When the value matched is a variable that the expected type mentions, each arm is checked against the type with the variable replaced by that arm's constructor. So `fn go ps acc -> f : …, f~format_type ps` can return a `String` in the `[]` arm and a lambda in the `Str :: rest` arm. Types that still contain an unknown (`_`) are not refined.

### 5.3 Recursion and totality
All code that may appear in types or proofs must be **total**:
- **Structural recursion** is compiled to recursors (D4).
- **Well-founded recursion** via a measure (required for merge sort, quicksort, etc.). The termination measure is a proof obligation like any other, so it goes to Z3 (D55). In the kernel this corresponds to recursion on the accessibility predicate `Acc` of `<` on `Nat` (lexicographic for tuples).
- **Surface form:** `decreasing e` on the first line of a function body gives the measure. `e` is a `nat` or a tuple of `nat`s, compared lexicographically. Mutually recursive functions share one measure space; each call must strictly decrease it (worked example: `value`/`array`/`elements` in `examples/json.ck`).
- **Recursion through containers** (`map depth items` where `items` is a field of the value being recursed on) is accepted as structural. The elaborator inserts the membership proof, as Lean's `List.attach` does by hand.
- Non-terminating code (server loops, actor bodies) is marked `partial` and lives in the `Div` effect (§8). `partial` code may never appear in a type or proof.

---

## 6. Modules and sealed interfaces

A module is a file. Its interface is the set of names marked `export` together with their **types only**.

Rules:
1. An exported definition is **sealed**: outside the module it behaves as an opaque constant. Its type is visible; its body never unfolds during conversion. This is enforced in the core (δ-reduction is blocked by module), not by name hiding, so "seeing past the interface" is impossible by construction.
2. **What an export shows:**
   | Declaration | Visible to importers |
   |---|---|
   | `export fn` | name + full constraint list (pre- and postconditions are the contract) |
   | `export enum` / `export record` | type, constructors, fields, invariants |
   | `export abstract enum/record T a +b` | the type constructor and its parameter polarities only (D16) |
   | `export lemma` | statement only |
   | `export transparent fn` | everything, including the body (it unfolds in conversion and in the solver) |
3. **Proofs are part of the interface.** Because bodies are sealed, a library must export the lemmas and postconditions its users need. A sorting module exports `sort` *and* `sort_sorted`, `sort_perm`. This is how libraries "ship with proofs."
4. `export transparent`: use sparingly; the body becomes part of the stable interface. Typical use: small definitional helpers that specifications are written in terms of (`list.keys`, `len`).

5. **Files (D53).** `import a.b` finds the standard-library module `a.b`, or else the file `a/b.ck` beside the file being checked; that file declares `module a.b`. Checking a program checks every module it imports, including their proofs, and `checkers trust` prints the ledger of all of them.
6. **What sealing means for proofs (D54).** In an importer's queries a sealed function is uninterpreted: the importer knows exactly its postconditions and the lemmas it brings in with `have`, nothing about its body. A fact the library does not export cannot be proven outside it; the library has to export a lemma (rule 3).

Background: Rossberg, Russo & Dreyer, *F-ing Modules* (JFP 2014) for sealing; Gratzer, Sterling et al., *Controlling Unfolding in Type Theory* for why sealing must live in conversion in a dependent setting.

---

## 7. Theorem prover

### 7.1 Obligations
Elaboration produces obligations `Γ ⊢ φ` with `φ : Bool`. Sources, each reported at its own span:

| Obligation | Where | Goal |
|---|---|---|
| precondition | every call of a function with predicates over its parameters (including refinement-alias parameter types such as `b~U8`) | the predicates, with the arguments substituted |
| postcondition | the end of a function body | the predicates mentioning the result, with the body substituted |
| constructor invariant (D11) | every constructor application | the constructor's predicates, including refinement-alias field types |
| weakened refinement (D83, proposed) | a value whose refinement is replaced by a weaker one in a covariant position (`List (n~Int, n >= 6)` as `List (n~Int, n >= 5)`) | for any `n`: the found predicates imply the expected ones |
| call of a function-typed value (D84, proposed) | `f a` where `f`'s type has preconditions | the preconditions at `a`; afterwards its postconditions at `a` and `f a` are facts |
| function passed as a value (D85, proposed) | a named function, partial application or lambda passed where a function type is expected | for any argument: the expected precondition implies the function's own; with it, the function's postcondition implies the expected one |
| refined type argument (D71) | a value checked against a refinement alias that the call or constructor it is passed to doesn't already check: one that comes from a type argument (`n` in `n :: xs : List Small`, `Some n : Option U8`, a list literal's elements, a tuple's components, a lambda's result). Not for a value whose type is already that alias, and not for an operand of an arithmetic or comparison operator (`10` in `x < 10` with `x~Small`) | the alias's predicates, with the value substituted |
| `Nat` subtraction (D6) | `a - b` on `Nat` | `a >= b` |
| division | `a / b`, `a % b` | `b != 0` |
| index | `src[i]` | `i < len src` |
| lemma | a `lemma` without a proof, or `auto` in a proof | its `ensures`, or the current goal |
| `have e` (D49) | a `have` of a `Bool` | `e` |
| `check` | `check e` | evaluated (D40), no solver |

Predicates inside types and specifications are not themselves checked for well-definedness (a precondition of a function called in a postcondition is not an obligation).

Γ, the **facts in scope**, contains: the preconditions of the enclosing function; the definitions of `let`-bound variables; `n >= 0` for every `Nat`; **path conditions**, namely the guards of enclosing `if`s (true in `then`, false in `else`), the left operand of a short-circuiting `and`/`or`/`implies`, the constructor equation of the current `match` arm (`xs == y :: rest`) together with that constructor's invariants, the literal of a literal arm or the negations of the others in its `_` arm, and an arm's guard; the `ensures` of every lemma brought in with `have`, and every `have` fact (D49); and the postcondition of every function applied in the goal or the facts (D50).

### 7.2 Discharge pipeline
Tried in order; first success wins:
1. **Compute:** a `check` is evaluated at compile time (D40).
2. **SMT:** translate Γ and ¬φ to SMT-LIB and ask the linked-in Z3 (§7.3, D46). On `unsat`, φ is proven, and the ledger records `smt φ` with the query's hash. Each query is first tried with every reflected definition uninterpreted: that is weaker, so `unsat` is still a proof, and it is fast when the facts in scope (`have`) already suffice. Only then is it tried with the definitions, which Z3 unfolds.
3. **User proof:** a `lemma`'s `proof` block (D13, D49), or `have` facts added before the obligation arises.

On failure (D48), the error shows the obligation, the facts in scope, and Z3's counterexample when one exists.

### 7.3 SMT fragment (v0.1)
Decidable fragment, following Liquid Haskell: quantifier-free linear integer arithmetic, booleans, equality, datatypes, arrays and uninterpreted functions. Mapping:

| Checkers | SMT-LIB |
|----------|---------|
| `Int`, `Nat`, `U8`, … | `Int`, with `n >= 0` for `Nat` and the alias's predicates for refinements |
| `Bool` | `Bool` |
| `==`, `!=`, `<`, `<=`, `+`, `-`, `*`, `/`, `%` | native (`div`, `mod`: Euclidean, like Checkers) |
| `Bytes` | `(Seq Int)`; `len`, `src[i]`, `++` native; each `src[i]` is known to be `< 256` |
| `String` | its UTF-8 bytes, `(Seq Int)` (D58): `len` (bytes, not characters), `++` and `utf8.encode` native |
| `Bag` (D47) | `(Array Int Int)` |
| enums, records, `List`, `Option`, `Result`, tuples | `declare-datatypes`, with type parameters (value parameters are dropped from the sort); a value's constructor invariants are assumed, with the value parameters of its type filled in (`p~Parsed Json src i` gives `p.stop <= len src`) |
| type variables, abstract types | uninterpreted sorts |
| a parameter of function type | an uninterpreted function; a known function argument (a named function, a lambda without free variables) is specialized (D57) |
| function `f` defined in this module, or imported `transparent` | **reflected** (D12) as `define-fun-rec`, instantiated per type; Z3 unfolds the definition where needed |
| other imported functions, builtins | uninterpreted, plus their postconditions |
| `match`, `if`, `let` | `ite` on testers, `let` |

Lambdas, partial applications and effects (`when`, `fork`, `join`) are outside the fragment (E0451); prove facts about them with a lemma.

Z3 sees more values than the program can build: `Option Nat` is `Option Int` to it, and neither a record's invariant nor a function's precondition is part of a sort. So a fact about all values of a type is assumed only where it holds for all of Z3's values too. A `Nat` result of `f` is assumed `>= 0`:
- at each call in the query, under `f`'s precondition, like a postcondition;
- for every argument, including in terms Z3 creates by unfolding definitions, only if that holds for every solver value: `f` is not reflected (then it is free), or `f` has no precondition, recurses only structurally, and its body is built from non-negative parts (`0`, `1 + length rest`, other such functions). `max_of`'s `if x > m then x else m` is not such a body, so `max_of xs >= 0` is known only where `max_of xs` appears in the query; `have max_of xs >= 0` puts it there.

If Z3 rejects a query, which is a checkers bug, the obligation is reported unproven, never proven. **Known gap:** a reflected definition is given to Z3 as an equation for all values, including ones on which a `decreasing` recursion would not end; Dafny and F\* avoid this with typing predicates and fuel, which is the planned fix.

Lemmas are not added automatically; `have` brings one in. **(proposed)** An `@auto` attribute on an exported lemma adds it to every query in importing modules (F\*'s SMT patterns), for very common facts only.

### 7.4 Trust ledger (D1)
Each module records every fact it relies on without a kernel-checked proof: obligations proven by Z3 (kind, location, Z3 version, query hash), `admit`s, and `check`s proven by evaluation. `checkers trust FILE.ck` prints the ledger of a file. This is the only place Z3 enters the trust base, and the hook for future certificate checking.

`admit` (D13) is recorded as an unproven assumption. Development builds allow it; `checkers build --release` (later) will reject any module whose transitive ledger contains one.

### 7.5 Refined types inside types (M10, D82–D87) **(proposed)**

D71 made a refinement inside a type mean what it says, for refinements written as aliases. M10 lets them be written in place, puts predicates on function types, and compares refinements by implication.

```
type Big = n~Int, n >= 5

fn at_least k x -> y : k~Int, x~Int, x >= k, y~Int, y >= 0
    x - k

# D82: an inline refinement; the same type as `List Big` (D83).
fn shift xs -> ys : xs~List (n~Int, n >= 5), ys~List (m~Int, m >= 0)
    list.map (at_least 5) xs          # D86: allowed; D85: `n >= 5 ⇒ n >= 5`

# D84: the call obliges `x >= 5`; its result is known to be `>= 0`.
fn apply f x -> r : f~(x~Int -> y~Int, x >= 5, y >= 0), x~Big, r~Int, r >= 0
    f x
```

Failures:

```
fn too_strict xs -> ys : xs~List Big, ys~List Int
    list.map (at_least 7) xs
```

```
error[E0450]: cannot prove that `at_least 7` can be called here
 --> example.ck:2:14
  |
2 |     list.map (at_least 7) xs
  |              ^^^^^^^^^^^^ `list.map` may call this with any `Big`
  = note: it needs `x >= 7`
  = note: counterexample: x = 5
  = help: pass a function that accepts every `Big`, or narrow what `xs` holds
```

**How it is checked.** An inline refinement is an anonymous alias, so D71's machinery applies unchanged: obligations where a value is built, variance through type arguments. What changes is the comparison of two refinements in one position: by implication for any value (D83), proven by Z3, where D71 asked for the same alias. For function types the comparison runs both ways (D85): preconditions contravariantly, postconditions covariantly. All of these are about one value or one argument at a time, so they need no induction.

**What stays out.** Gaining a refinement through a type argument of an existing value (`List Int` as `List Big`) still needs a proof about every element: still E0262, until the prover supports induction for it (D71). Function types in types (a list of refined functions) follow the same rules through variance.

---

## 8. Effects, capabilities, and concurrency

Decisions D27–D35. Worked examples: `examples/wc.ck` (a CLI tool using authority capabilities), `examples/copy.ck` (linear resources), `examples/log.ck` (cowns and `when`), `examples/parallel.ck` (`par`, `fork`, `join`).

### 8.1 Why capabilities

Every Checkers function is a mathematical function: the prover relies on `f x == f x`. A side-effecting call such as reading a file would break that if it were an ordinary application of ordinary values. Checkers keeps it sound the way Idris 2 and Clean do: every effectful operation takes a **capability**, and the kernel treats capabilities as linear (multiplicity 1, §2), so no two effectful calls ever receive the same token and none of them can be proven equal to another.

A capability is also an **authority**: code can only touch what it is handed. A JSON library that never receives an `Fs` cannot read files, and its type proves it.

Capabilities come in two kinds (D28):

| Kind | Examples | Surface behaviour | Ordering proven? |
|---|---|---|---|
| **Authority** | `System`, `Term`, `Fs`, `Env`, `Proc`, `Net`, `Clock`, `Sched` | copied on use, dropped when unused; written without `own` | no |
| **Resource** | `File`, `Child`, `Pipe`, `Socket` | linear by type (D39): used exactly once, threaded with `<-`, closed explicitly; `own` may be written | yes |

### 8.2 The root capability and `main` (D27, D31)

```
export fn main args sys -> code : args~List String, sys~System, code~ExitCode
```

The runtime calls `main` with the command-line arguments and the root capability. `System` is a prelude record of authority capabilities:

| Field | Type | Authority |
|---|---|---|
| `term` | `Term` | stdin, stdout, stderr, terminal modes |
| `fs` | `Fs` | the file system |
| `env` | `Env` | environment variables, working directory |
| `proc` | `Proc` | spawning and signalling processes |
| `net` | `Net` | sockets |
| `clock` | `Clock` | time, sleeping |
| `sched` | `Sched` | creating cowns and scheduling behaviours (§8.5) |

A program takes what it needs with a record pattern, `let System { fs, term } = sys`, or a field, `sys.fs`. Capabilities can be **attenuated**: `files.within dir fs` returns an `Fs` confined to `dir`. Passing only an attenuated capability to a function bounds what it can do.

`ExitCode` is an enum: `Success`, `Failure n` with `n~U8, n > 0`.

### 8.3 Authority capabilities: copied on use (D28)

An authority capability can be used any number of times. Operations on it return only their result:

```
let contents = files.read path fs
let listing  = files.list_dir dir fs
terminal.print_line "done" term          # as a statement, see below
```

**How this stays sound.** The elaborator gives every use of an authority variable its own fresh token, inserting the splits itself:

```
let a = files.read "x" fs        # written
let b = files.read "y" fs

let (fs1, fs2) = split fs        # checked by the kernel
let a = files.read "x" fs1
let b = files.read "y" fs2
```

The kernel still checks exact linearity, and no two calls share a token. When a capability goes unused, the elaborator inserts `drop`.

**What it costs.**
1. *No proven ordering between uses of one authority.* At runtime, calls run in program order. The prover, however, treats two uses of `fs` as independent, so "a read after a write returns what was written" is not provable through `Fs`. Orderings that need proofs go through resources (§8.4).
2. *Closures that capture an authority are single-use.* `let g = \u -> files.read p fs` captures one token, so `g` may be called once; the compiler rejects a second call and suggests passing `fs` as a parameter. Behaviour bodies (`fork`, `join`, `when`) run once, so they may capture authorities freely; the enclosing code keeps using them.
3. *Concurrent branches can race on the operating system* (two forks writing one file), as in any language.

**Effect statements.** A call whose result is `Unit` may stand alone as a statement line in a block, e.g. `terminal.print_line "done" term`. Only calls returning `Unit` may: discarding any other value needs `let _ = …`.

### 8.4 Resources: linear, threaded with `<-` (D29)

A resource is an open, stateful thing that must be released: an open `File`, a `Child` process, a `Pipe`, a `Socket`. It has multiplicity 1, implied by its type (D39), and must be consumed exactly once, as must any value that contains one. A generic function accepts a resource only through an `own` parameter (`v~own a`, D45). Forgetting to `close` a file or `wait` for a child is a compile error, which proves, for free, that the shell reaps every child it spawns.

Operations on a resource consume it and return a fresh one together with their result, `(result, resource)`, with the resource last. `<-` rebinds it:

```
line <- file.read_line f         # means: let (line, f) = file.read_line f
_ <- file.write b f
files.close f
```

The **last argument** of the call must be a resource variable. Because each operation consumes the previous token, the prover sees the operations in sequence; this is where ordering proofs about effects (§8.8) live.

Resources are created from authorities, e.g. `files.open path fs` returns `Result File IoError`.

### 8.5 Concurrency: cowns and `when` (D30)

Data is immutable, so sharing it never races; parallel evaluation of pure code is always safe (`par`, §8.6). What needs coordination is a **resource or state shared by several concurrent tasks**: a table of running jobs, the terminal. For that, Checkers adopts Verona's *behaviour-oriented concurrency* (Cheeseman et al., OOPSLA 2023):

- A **cown** (concurrent owner) wraps a value. `let c = cown.new v sched` creates a `Cown a`. The cown handle may be freely shared; its *contents* are owned by the cown, and a resource moved into a cown (e.g. an open `File`) is no longer available to the creator.
- A **behaviour** gets exclusive access to one or more cowns:

  ```
  when l = log, n = total using sched
      terminal.print_line (format (len l)) term
      (l, n + 1)
  ```

  This *schedules* the body, which runs once it holds all the listed cowns at once. Inside, `l` and `t` are the current contents, with full ownership, and the body evaluates to the new contents (a tuple, in the order listed; a single value for one cown). `when` is a statement. The body may use authority capabilities from the enclosing scope (here `term`) and may schedule further behaviours with `sched`.

Guarantees, by construction:
1. **No data races.** Contents are only reachable inside a behaviour holding that cown.
2. **No deadlock.** All of a behaviour's cowns are acquired atomically; there are no locks to order.
3. **Causal order.** Two behaviours that share a cown run in the order they were scheduled.

**Invariants.** A cown's content type can be a refinement (`type Log = entries~List String, len entries <= 100`). Every behaviour must return contents of that type, so it must re-establish the invariant: this is the lock-invariant rule of concurrent separation logic, enforced by ordinary type checking. Concretely, the prover checks two obligations (E0450): every value a `when` body hands back satisfies the refinement ("the invariant of a cown holding `Log`"), and so does the value given to `cown.new` when the expected type is `Cown Log` (D71). Inside the body, the invariant of each cown held is a fact. A cown's type must match exactly (D71): a `Cown Nat` is never a `Cown Log`, so give the type where the cown is created, in the signature of the function that creates it (`fn new_log sched -> c : sched~Sched, c~Cown Log`).

**Results.** `when` is asynchronous: it schedules the body and continues immediately, so the body's only outputs are the new contents of its cowns. A later behaviour on the same cowns sees them. To compute values in parallel and combine them, use §8.6.

**Actors** are a library on top: an actor is a cown holding its state, and sending a message schedules a `when` on it. Session-typed channels (Neykova & Yoshida) can be layered the same way later.

### 8.6 Parallelism and fork/join (D33, D34)

Nothing ever blocks waiting for another task; this is what keeps deadlock impossible. Parallel work comes in two forms.

**Pure: `par`.**

```
let (l, r) = par (sort left, sort right)
let (a, b, c) = par (f x, g y, h z)
```

`par` takes a tuple literal with two or more components, evaluates them in parallel (work-stealing tasks), and returns the tuple. The components must be pure: no capabilities, no `partial` calls. Pure code holds no cowns and schedules nothing, so the implicit join is safe. To the prover `par t` is `t`, so a parallel `sort` keeps its proof, stays a pure function, and can be used in types.

**Effectful: `fork` and `join`.**

```
a <- fork using sched
    files.read "a.txt" fs
b <- fork using sched
    files.read "b.txt" fs
done <- join x = a, y = b using sched
    combine x y
```

- `f <- fork using sched` + block schedules the block as a behaviour and binds `f~Future t`, where `t` is the block's type.
- `r <- join x = f1, y = f2, … using sched` + block schedules a behaviour that runs after every listed future has been filled. Inside, `x`, `y`, … are the plain values (moved out of the futures; each future can be joined once). It binds `r~Future t` for the block's result, so joins compose.
- A future is a cown that only its own fork or join can fill, and that fork/join is the first behaviour scheduled on it. A later join on that future is ordered after it (causal order, §8.5), so its value is always present: no `Option`, no waiting, no deadlock.
- Behaviour bodies may use authority capabilities from the enclosing scope (each use gets its own token, §8.3) and may fork, join and `when` further.
- A resource used inside a `fork`, `join` or `when` body **moves** into the behaviour and is no longer available outside it. Two concurrent branches therefore can never share an open `File`.

**Ending the program.** The process exits once no scheduled work remains. If `main` returns a `Future ExitCode`, that future's value is the exit code; this is how a program whose result comes from a join reports it.

### 8.7 Other effects

- **Non-termination:** `partial fn` (§5.3). A `partial` function cannot appear in types or proofs.
- **Errors:** `Result` and `try` (D14). No exceptions.
- **Algebraic effect handlers** (Koka, Effekt): not planned. Capabilities and `Result` cover the needs so far, and handlers complicate the prover.

### 8.8 Proofs about effectful code (later)

Capabilities and cown contents correspond to separation-logic resources (Iris, F\*'s Pulse). M3–M5 prove pure code. **A protocol is proved as a pure state machine (D81):** keep its state in a cown whose content type is a refinement (the protocol's invariant, §8.5), and make every behaviour apply a pure, verified transition function; the cown invariant obligations then prove the protocol at every step. Specifications over capability state itself (e.g. "after `files.write p b fs`, `files.read p fs'` returns `b`") are not scheduled.

### 8.9 Staging (M6, D7, D59–D64)

Underneath is Two-Level Type Theory (Kovács 2022): a compile-time stage and a runtime stage, with `Code a` (Kovács's ⇑a) for compile-time values that *are* runtime code, `quote e : Code a` for `e : a`, and `splice c : a` for `c : Code a`. Staging evaluates the compile-time stage away; the result is always a well-typed runtime program with no `quote`/`splice` left (Kovács §2.1.3, §5). The surface keeps all of that implicit in the common case:

```
# `n` is known at compile time; `x` is not.
fn power n x -> y : n~comptime Nat, x~Int, y~Int
    decreasing n
    if n == 0 then 1 else x * power (n - 1) x

fn cube x -> y : x~Int, y~Int
    power 3 x               # staged to: x * (x * (x * 1))
```

- **`comptime` binders (D59).** `x~comptime T` marks a compile-time parameter, like `ghost` and `own`. Every call must supply a value known at compile time: a literal, a `let` constant, another `comptime` parameter, or the result of compile-time code. Inside the body, code that depends only on compile-time values runs at compile time: `if`/`match` on them pick a branch, and recursion on them unrolls. Everything else becomes runtime code.
- **Stage inference (D60).** The elaborator inserts `quote` and `splice` itself, by Kovács's coercive subtyping (`a ≤ Code a` and back, §2.3.2): `Code`, `quote` and `splice` are written only by code that builds code explicitly (a generator returning `Code (Int -> Int)`). A runtime value never becomes a compile-time one; asking for one is an error with the value's span. **Not yet implemented:** M6 delivers the implicit form only; writing `Code`, `quote` and `splice` comes later. Until then a compile-time function's runtime parameters play the role of `Code` values: they are passed as code, and expansion inserts them.
- **Proofs (D61).** Obligations of a function with `comptime` parameters are proven once, with those parameters symbolic, so they hold for every specialization; staged output is not re-proven. Compile-time recursion obeys the termination rules of §5.3 (no `partial`), so staging always ends.
- **What exists at compile time (D62).** Pure code over `Nat`, `Int`, `Bool`, `Char`, `String`, `Bytes`, enums, records, lists and tuples of these, types, and functions. No capabilities or effects: compile time can't read files or the clock.
- **Errors.** E0270: an argument for a `comptime` parameter depends on a runtime value. E0271: a compile-time function used other than in a complete call (passed as a value, or partly applied); wrap it in a lambda. E0272: `comptime` on a `partial` function or a lemma. E0273: compile-time evaluation failed (a computation staging needs stopped with a runtime error).
- **Types compute.** A `comptime` argument's type may be computed from it (`format_type (pieces (string.bytes s) 0 [])`). The type checker evaluates such types by unfolding definitions; the standard-library primitives `string.bytes` and `utf8.encode` compute on literals there. Functions that compute types must be visible where they are used: exported `transparent` (D54) if they are used from another module.
- **Expansion.** A function with `comptime` parameters is a compile-time function: every call is expanded in place (that is what makes `if n == 0` decidable there). When an expansion reaches a call of the same function with the same compile-time arguments (recursion on runtime values, like `count c src (i + 1)`), it becomes one generated runtime function for those arguments, `count[10]`, and both calls call it (D64). Compile-time arguments that change at every step would need unboundedly many functions: E0273. Its runtime arguments are `let`-bound first unless they are variables, so each is evaluated exactly once, in order (D41). Known computations in the expanded code run at compile time; anything that fails there (a runtime error) is left for run time, unless staging needs its value (a `comptime` argument, a `match` it must decide), which is E0273.
- **Output.** Staging runs after checking and before erasure (§13.1). `checkers stage FILE.ck` prints each staged definition; `CHECKERS_DUMP=1` shows them too. Golden tests in `tests/stage/` pin staged code.

Worked example: `examples/format.ck`, a typed `fmt` whose format string is `comptime`. `fmt "{} is {n} years old"` has type `String -> Int -> String`, computed at compile time (`{}` takes a `String`, `{n}` an `Int`), and stages to

```
fn greet name age =
    let acc = "" ++ name
    let acc1 = acc ++ " is "
    let acc2 = acc1 ++ (format age)
    let acc3 = acc2 ++ " years old"
    acc3
```

with no format string left to parse at run time. A bad placeholder is a compile-time error: its type is `BadPlaceholder`, so `fmt "{x}" name` reports too many arguments for a `BadPlaceholder`, and `fmt`'s precondition `valid (string.bytes s) 0` catches the rest.

---

## 9. Surface language

The worked example for this section is `examples/json.ck`: an RFC 8259 parser and renderer whose bounds checks, termination, error positions, and object-key uniqueness are proven, plus a round-trip theorem. Decisions: D8–D23.

### 9.1 Lexical structure

**Logical lines (D23).** Source is split into logical lines, Python-style. A physical newline does **not** end a logical line when:
1. it is inside `(…)`, `[…]`, or `{…}`;
2. the line's last token is `,` or a binary operator (`+ - * / % ++ :: == != < <= > >= and or implies $ .` and the type operator `->` **inside brackets only**); or
3. the next line's first token is a binary operator from that list, or `:`.

A trailing `->`, `=` or `<-` outside brackets does **not** continue the line; it opens a block (a match arm body, a multi-line `let`). Indentation uses spaces only; a tab in leading whitespace is an error. When a logical line is followed by a more-indented line, the lexer emits `INDENT`; on return to an enclosing level it emits matching `DEDENT`s (an inconsistent dedent is an error). Blank and comment-only lines are ignored for layout.

**Comments:** `#` to end of line.

**Greedy tokens:** `<-` is always one token, so `x<-1` is a bind, not a comparison; write `x < -1`.

**Identifiers:**
- `lname` — `[a-z_][A-Za-z0-9_]*`: values, functions, parameters, fields, modules, type variables.
- `Uname` — `[A-Z][A-Za-z0-9_]*`: types, type constructors, data constructors, and constants (`SCREAMING_SNAKE_CASE` is a `Uname` too; D21 says which spelling belongs where).

**Literals (D19, D20):**
| Form | Type | Example |
|---|---|---|
| integer | `Int`/`Nat`/`U8`… by expected type | `42`, `0x20`, `1_000` |
| `'…'` | `U8` | `'"'`, `'\n'`, `'\\'`, `'\''`, `'\x7f'` |
| `c'…'` | `Char` | `c'é'`, `c'\u{1F600}'` |
| `"…"` | `String` (UTF-8) | `"'"`, `"a\u{e9}"`, escapes `\" \\ \n \r \t \0 \u{…}` |
| `b"…"` | `Bytes` | `b"null"`, escapes as strings plus `\xNN` |

**Keywords:** `module import as export abstract transparent fn enum record type let lemma ensures proof have auto admit check match if then else try and or implies decreasing partial ghost own comptime when using par`. `fork` and `join` are **contextual**: they are keywords only in `fork using …` and `join name = …` (right after `<-`), so `join` remains usable as an ordinary function name. `not` is an ordinary prelude function.

**Glued vs spaced (D22):** `.` and `[` with no whitespace before them, directly after an identifier, `)` or `]`, are field/module access and indexing. With whitespace before them they are composition and a list literal.

### 9.2 Grammar (EBNF)

`NL`, `INDENT`, `DEDENT` come from §9.1. `{x}` is zero or more, `[x]` optional. `lname`, `Uname` from §9.1.

```
file        ::= 'module' qname NL { import NL } { decl }
import      ::= 'import' qname [ '(' name { ',' name } ')' ] [ 'as' lname ]
qname       ::= lname { '.' lname }                          -- glued dots
name        ::= lname | Uname

decl        ::= [ 'export' [ 'abstract' | 'transparent' ] ] decl_body | check
decl_body   ::= fn | enum | record | alias | lemma | const
fn          ::= [ 'partial' ] 'fn' lname { lname } [ '->' lname ] [ ':' constraints ] NL
                INDENT [ 'decreasing' expr NL ] block DEDENT
enum        ::= 'enum' Uname { param } [ ':' constraints ] NL INDENT { ctor NL } DEDENT
ctor        ::= Uname { lname } [ ':' constraints ]
record      ::= 'record' Uname { param } [ ':' constraints ] NL INDENT { field NL } DEDENT
field       ::= lname '~' [ 'ghost' ] expr { ',' expr }      -- the field's own constraint list
param       ::= [ '+' | '-' ] lname                          -- polarity only on abstract types (D16, E0360)
alias       ::= 'type' Uname { lname } '=' constraints NL    -- first constraint must be `x~T`
lemma       ::= 'lemma' lname { lname } [ ':' constraints ] NL INDENT
                { 'let' pattern '=' expr NL } 'ensures' expr NL
                [ 'proof' NL INDENT block DEDENT ] DEDENT
const       ::= 'let' Uname '=' expr NL                      -- compile-time constant
check       ::= 'check' expr NL                              -- compile error unless true

constraints ::= constraint { ',' constraint }
constraint  ::= lname '~' [ 'ghost' | 'own' | 'comptime' ] expr  -- typing; in a type, '(' constraints ')' is a refinement and
                                                                --   '(' [lname '~'] expr '->' [lname '~'] expr { ',' expr } ')' a refined function type (D82, proposed)
              | expr                                         -- predicate (Bool or Prop)

block       ::= { stmt NL } expr NL
stmt        ::= 'let' pattern '=' ( expr | NL INDENT block DEDENT )
              | 'have' expr                                  -- lemma application; adds its conclusion
              | expr                                         -- D35: must have type Unit
              | pattern '<-' expr                            -- D29: rebinds the call's last argument
              | 'when' lname '=' expr { ',' lname '=' expr } 'using' lname NL
                INDENT block DEDENT                          -- D30: schedule a behaviour
              | pattern '<-' 'fork' 'using' lname NL INDENT block DEDENT                          -- D33
              | pattern '<-' 'join' lname '=' expr { ',' lname '=' expr } 'using' lname NL
                INDENT block DEDENT                          -- D33
expr        ::= 'if' expr 'then' expr 'else' expr
              | 'if' expr NL INDENT block DEDENT
                'else' ( 'if' … | NL INDENT block DEDENT )   -- `else if` chains; `else` is required
              | 'match' expr NL INDENT { arm } DEDENT
              | '\' apat { apat } '->' ( expr | NL INDENT block DEDENT )   -- lambda; block body only outside brackets
              | 'try' expr                                   -- D14
              | 'par' '(' expr ',' expr { ',' expr } ')'     -- D34
              | 'auto' | 'admit'                             -- proof blocks only
              | opexpr                                       -- precedence climbing over §9.4
arm         ::= pattern [ 'if' expr ] '->' ( expr NL | NL INDENT block DEDENT )
app         ::= postfix { postfix }                          -- juxtaposition, left-assoc (D8)
postfix     ::= atom { '.' lname | '[' expr ']' }            -- glued only (D22)
atom        ::= lname | Uname | literal
              | '(' ')' | '(' expr ')' | '(' expr ',' expr { ',' expr } ')'
              | '(' op ')' | '(' op expr ')' | '(' expr op ')'    -- operator sections
              | '[' [ expr { ',' expr } ] ']'
pattern     ::= cpat { '|' cpat }                            -- or-patterns
cpat        ::= apat '::' cpat | Uname { apat } | Uname '{' fieldpat { ',' fieldpat } '}' | apat
fieldpat    ::= lname [ '=' pattern ]                        -- D32
apat        ::= '_' | lname | literal | Uname
              | '(' pattern ')' | '(' pattern ',' pattern { ',' pattern } ')'
              | '[' [ pattern { ',' pattern } ] ']'
```

`if`, `match`, lambdas and `try` extend as far right as possible; as an argument they need parentheses or `$` (`map (\x -> x + 1) xs`, `f $ \x -> …`).

### 9.3 Constraints: the one place types appear (D9)

| Form | Meaning | Core |
|---|---|---|
| `x~T` | `x` has type `T` | `(x :ω T)` |
| `x~ghost T` | exists only for types/proofs | `(x :0 T)` |
| `x~own T` | used exactly once; implied for resources (D39), written on generic parameters that may receive one (D45) | `(x :1 T)` |
| predicate over inputs only | precondition | refinement on the inputs |
| predicate mentioning the result name | postcondition | return type `{r : R \| P}` |
| predicate in a constructor/field list | invariant (D11) | `Prop` field, erased |
| free `lname` in a type position, not in scope (`a` in `xs~List a`) | implicit type parameter (D10); a name used as a qualifier (`future` in `future.Future`) is never auto-bound | `{a :0 Type}` |

A constraint is only required where inference fails; `fn is_ws b : b~U8` infers its `Bool` result.

| Surface | Core (§3, §5) |
|---|---|
| `fn f x y -> r : x~A, p x, y~B, r~R, q x y r` | `def f : (x :ω A) → (_ :0 p x) → (y :ω B) → {r : R \| q x y r}` |
| `enum Option a : a~Type` + `None` / `Some x : x~a` | inductive `Option (a : Type)` with two constructors |
| `Obj fields : fields~List (String, Json), unique (keys fields)` | constructor `Obj : (fields :ω …) → (_ :0 unique (keys fields)) → Json` |
| `record R p : p~T` + fields | single-constructor inductive + projections `r.field` |
| `type Hex16 = n~Nat, n < 0x10000` | `def Hex16 := {n : Nat \| n < 0x10000}` (transparent) |
| `lemma l xs : C` / `ensures φ` / `proof …` | `def l : (xs …) → (_ :0 C) → φ`, `φ : Prop`, all erased |
| `let x = try e` (D14) | `match e` with `Ok v -> v`, `Err x -> return (Err x)` from the enclosing `fn` |

### 9.4 Operators (high to low precedence)

| Level | Operators | Assoc. |
|---|---|---|
| 11 | glued `.field`, `.name`, `[i]` | left |
| 10 | application (juxtaposition) | left |
| 9 | `.` (spaced: composition) | right |
| 8 | unary `-` | prefix |
| 7 | `*` `/` `%` | left |
| 6 | `+` `-` `++` | left |
| 5 | `::` | right |
| 4 | `==` `!=` `<` `<=` `>` `>=` | none |
| 3 | `and` | right, short-circuit |
| 2 | `or` | right, short-circuit |
| 1 | `implies` | right |
| 0.5 | `->` (function type: `f~(a -> b)`) | right |
| 0 | `$` | right |

Every binary operator `op` is also the function `(op)`, curried. Inside a match guard `->` ends the guard, so a function type there needs parentheses. As in Haskell, `f -1` is subtraction; pass a negative argument as `f (-1)`. In patterns `-1` is a literal (`Num -1 -> …`). `a[i]` requires `i < len a`; `/` and `%` require a non-zero divisor. `==` follows D18.

### 9.5 Compound types and containers (prelude)

All prelude types are immutable.

| Type | Kind | Notes |
|---|---|---|
| `Type`, `Prop` | universes | D3 |
| `Bool`, `Unit` (`()`) | enum | |
| `Int`, `Nat` | builtin | arbitrary precision (D6) |
| `U8`, `U16`, `U32`, `U64`, `I8` … `I64` | refinement aliases of `Int`/`Nat` | D6 |
| `Char` | refinement of `Nat` | Unicode scalar value (no surrogates) |
| `(a, b, …)` | tuple | core Σ type; `.0`, `.1` or patterns |
| `Option a` | enum | `None`, `Some x` |
| `Result a e` | enum | `Ok x`, `Err x`; works with `try` |
| `List a` | enum | `[]`, `x :: xs`, `[1, 2]` |
| `Bytes` | builtin | O(1) `len` and index; `b"…"` |
| `String` | builtin | valid UTF-8 (D20); `string.bytes s` gives its `Bytes` |
| `Array a` | builtin | O(1) index; persistent updates |
| `Map k +v`, `Set k` | abstract, sealed modules | ordered by `Ord k` (D15); export lemmas such as `lookup_insert` |

User-defined compound types are `enum` (sums, including recursive and indexed families) and `record` (products). Indexed families use equality constraints:

```
enum Vec a n : a~Type, n~Nat
    Nil          : n == 0
    Cons x xs    : x~a, xs~Vec a m, n == m + 1      # m auto-bound and erased (D10)
```

### 9.6 Target programs
- M3: `fn sort xs -> ys : xs~List Int, sorted ys, perm xs ys` (insertion sort).
- M5: `examples/json.ck` checks, with only its two `admit`s in the trust ledger.

### 9.7 Naming warnings (D21)

| Code | Rule | Applies to |
|---|---|---|
| W001 | must be `UpperCamelCase` | `enum`, `record`, `type` names; constructors |
| W002 | must be `lower_snake_case` | functions, lemmas, parameters, `let`/pattern variables, fields, module names, import aliases |
| W003 | must be `SCREAMING_SNAKE_CASE` | top-level `let` constants |

A name with a leading `_` is checked without it. Warnings never stop compilation; `--deny-warnings` turns them into errors.

Other warnings:

| Code | Rule |
|---|---|
| W010 | `own` on a type that is already linear (D45) |

---

## 10. Milestones

Reordered (D25) so that Checkers can run CLI tools before the prover exists.

| # | Deliverable | Done when |
|---|-------------|-----------|
| M0 | Rust workspace; lexer with layout (§9.1); parser for §9.2; naming warnings (§9.7); source-span diagnostics; `checkers parse` / `checkers check` | `examples/json.ck` and every spec example parse; golden tests for errors and warnings |
| M1 | Type checker: modules and imports, dependent types with implicit arguments (bidirectional elaboration, pattern unification), enums/records (strict positivity), `match` → case trees with exhaustiveness (D4), structural termination, `own`/`ghost` usage (QTT, §4), operators (D38), effect forms (§8) typed. **Not yet:** predicates are type-checked as `Bool` and recorded, but proven only in M3; `decreasing` measures are recorded and checked in M5; proof blocks and `check` evaluation come with M3 and M2; linearity of resources inferred from their *type* (not just `own` binders) comes with M2. | `Vec`, `List`, `Nat` programs type-check; all `examples/` type-check; golden contract tests in `tests/types/`, including rejected programs |
| M2 | Erasure and interpreter (§13), standard library builtins, capabilities and `main` (§8.2–8.4: `Term`, `Fs`, exit codes), `checkers run`, `check` evaluation (D40), resource linearity by type (D39), single-threaded behaviour scheduler (D44). **Not yet:** `Env`, `Proc`, `Net`, `Clock` operations. | `examples/wc.ck` and `examples/copy.ck` run; golden run tests in `tests/run/` |
| M3 | Obligations with facts in scope (§7.1), Z3 pipeline (§7.2, D46), refinement aliases, pre/postconditions, constructor invariants, lemmas and proofs (D49), `Bag` and `perm` (D47), trust ledger, `checkers trust` | verified insertion sort (`examples/sort.ck`); `examples/wc.ck` verifies |
| M4 | Module files (D53), sealing in conversion and in the prover (D54), exported lemmas, multi-module checking, transitive trust ledger | `examples/resort.ck` uses `sort` from `examples/sort.ck` through its exported lemma only |
| M5 | Well-founded recursion, lexicographic `decreasing` | verified merge sort; `examples/json.ck` checks (done 11/06/2026: its two `admit`s, `string_render` and `members_render`, and the axioms `decimal.render_starts` and `decimal.scan_json_render` are the trust ledger) |
| M6 | Two-level staging (`comptime`, §8.9, D59–D63) | `examples/format.ck` checks, runs and stages; `checkers stage`; golden tests in `tests/stage/` (done 11/06/2026) |
| M7 | Multi-threaded scheduler for cowns, `when`, `fork`/`join` and `par` (single-threaded since M2, D44); actor library | `examples/log.ck` and `examples/parallel.ck` run; stress tests show no races or deadlocks (done 11/06/2026) |
| M8 | Cranelift backend (§14, D72–D77): closure conversion, word representation, reference counting, tail calls, `checkers build`, lock-free scheduler | every `tests/run/` and `tests/stress/` case gives the same output natively (done); `wc.ck` at least 20× faster than the interpreter (done: 45×); ~~the fork/join tree of §13.7 no slower on 2 threads than on 1~~ replaced by D79: the tree with about 5 µs of work per leaf is faster on 2 threads (done: 1.35×) (done 11/06/2026) |
| ~~M9~~ | ~~Capstone: interactive shell~~ removed (D81): the shell is not part of this repository | — |
| M10 | Refined function types (D52, §7.5, D82–D87, proposed): refinements written inside types, predicates in function types, refinements compared by implication, preconditions checked and postconditions known at calls of function-typed values, partial applications everywhere (lifts D51, retires E0453) | `list.map (at_least 5) xs` checks when `xs~List (n~Int, n >= 5)`; every case in `tests/proposed/refined_fn_types.ck` gives the output marked there |

---

## 11. References

- Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS 2018. https://strathprints.strath.ac.uk/64031
- Brady, *Idris 2: Quantitative Type Theory in Practice*, ECOOP 2021. https://arxiv.org/abs/2104.00480
- Kovács, *Staged Compilation with Two-Level Type Theory*, ICFP 2022. https://arxiv.org/abs/2209.09729
- Kovács, *elaboration-zoo*. https://github.com/AndrasKovacs/elaboration-zoo
- de Moura & Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 2021. https://lean-lang.org/papers/lean4.pdf
- F*. https://fstar-lang.org/
- Vazou et al., *Refinement Types for Haskell*, ICFP 2014. https://goto.ucsd.edu/~rjhala/papers/refinement_types_for_haskell.html
- Rossberg, Russo & Dreyer, *F-ing Modules*, JFP 2014. https://people.mpi-sws.org/~rossberg/publications.html
- *Controlling Unfolding in Type Theory*. https://arxiv.org/pdf/2210.05420v2
- Agda opaque definitions. https://agda.readthedocs.io/en/stable/language/opaque-definitions.html
- Pony papers. https://www.ponylang.io/learn/papers/
- Neykova & Yoshida, *Multiparty Session Actors*, LMCS 2017. https://lmcs.episciences.org/3227
- Iris. https://iris-project.org/
- Cheeseman et al., *When Concurrency Matters: Behaviour-Oriented Concurrency*, OOPSLA 2023. https://2023.splashcon.org/details/splash-2023-oopsla/86/When-Concurrency-Matters-Behaviour-Oriented-Concurrency
- Borretti, *How Capabilities Work in Austral*. https://borretti.me/article/how-capabilities-work-austral
- Pulse (F\*), concurrent separation logic. https://fstar-lang.org/tutorial/book/pulse/pulse.html
- Vazou et al., *Refinement Reflection: Complete Verification with SMT*, POPL 2018. https://arxiv.org/abs/1711.03842
- RFC 8259, *The JavaScript Object Notation (JSON) Data Interchange Format*. https://www.rfc-editor.org/rfc/rfc8259

---

## 12. Development workflow (D24)

- `tests/` holds golden tests: each `NAME.ck` has a `NAME.out` with the exact expected compiler output (diagnostics or program output). `cargo test` runs them all.
  - `tests/parse/`: syntax tree plus parse and lint diagnostics.
  - `tests/check/`: parse and lint diagnostics only.
  - `tests/types/`: the full report, including type checking and proofs. These are the checker's contract: one file per rule area (mismatches, exhaustiveness, termination, usage, positivity, effects, modules, resources, `own`, proofs), with an accepted-programs file that must stay clean.
  - `tests/pending/`: the pinned output of examples listed in `examples/PENDING`, which need a later milestone (D48).
  - The prover tests need Z3 (D46).
- A report from Ian is "found X, expected Y" with a `.ck` snippet. It is added as a failing golden test first, then fixed. If Y changes the language, this spec is updated before the code.
- `UPDATE_GOLDEN=1 cargo test` rewrites `.out` files; every rewritten file is reviewed in the diff before committing.

---

## 13. Execution (M2; native since M8)

`checkers run FILE.ck [ARG…]` (D43) runs a program. Since D80 all evaluation is native code (§14): running programs, `check` declarations during `checkers check` (D40), and compile-time evaluation in staging (§8.9). Until then an interpreter (M2–M8) did it; this section describes the semantics, which native code keeps.

### 13.1 Erasure

Before running, the checked program is staged (§8.9): calls of compile-time functions are expanded, and what they compute at compile time is replaced by its value. Then it is erased: types, type arguments, implicit arguments, `ghost` parameters and fields, refinement predicates, `ensures` clauses and proofs disappear. What remains is an untyped functional program over numbers, strings, bytes, constructors, tuples, closures and capabilities.

### 13.2 Evaluation (D41)

- Strict and call-by-value. A call evaluates its arguments left to right, then the body.
- A block runs its lines in order. Effects (calls on `term`, `fs`, a `File`) therefore happen in program order.
- `and`, `or`, `implies` and `if` evaluate only the operands they need.
- `Nat` and `Int` are arbitrary-precision (D6). `/` and `%` are Euclidean (the remainder is never negative), matching the prover's integers.
- A tail call does not grow the stack, so a loop written as tail recursion (`count_from` in `wc.ck`) runs in constant stack space.
- `==` compares values structurally. Functions and capabilities cannot be compared; comparing them is a runtime error.
- `len` of a `String` is its length in bytes (UTF-8, D20).

### 13.3 Runtime checks

Since M3, the prover discharges every obligation before a program runs, so these checks never fail in a program that verifies. They remain for programs run with `checkers run --unverified` (D48), and for `check`s evaluated during checking. Native code checks the obligations that guard an operation, and stops the program if one fails:

| Operation | Checked condition |
|---|---|
| `a - b` on `Nat` | `a >= b` |
| `a / b`, `a % b` | `b != 0` |
| `src[i]` | `i < len src` |
| `main` returns `Failure n` | `1 <= n <= 255` |

A failure prints a runtime error that names the failing operation and the function it occurred in, and exits with code 70. Other refinements (a computed `U8` staying below 256, a postcondition) are not checked at run time; the prover proves them.

### 13.4 `main` and the root capability

`main` receives the command-line arguments after the file name, as `List String`, and the root `System` (§8.2). `term` reads standard input and writes standard output and error; `fs` is the process's file system with relative paths resolved against the current directory, and `files.within dir fs` confines it to `dir` (absolute paths and `..` are then refused). Operations on `env`, `proc`, `net` and `clock` are not implemented yet.

`IoError` values describe the operating-system error, as in `No such file or directory`. `read_line` (on `term` or a `File`) returns a line without its `\n`; bytes that are not valid UTF-8 become U+FFFD.

### 13.5 Behaviours (D44; M7: D66–D70)

`when`, `fork` and `join` schedule behaviours on a single FIFO queue that runs after `main` returns. The process exits when the queue is empty. If `main` returns a `Future ExitCode`, its value is the exit code.

**M7.** Behaviours run on a pool of worker threads:

- **Scheduling (D66).** Verona's algorithm (Cheeseman et al. 2023, §4): scheduling a behaviour appends it, in one atomic step, to the queue of every cown it names (a `fork` names a fresh future; a `join` names the futures it waits for). It runs when it is first in all of its queues, and on finishing it leaves them, which may make the next behaviours runnable. This gives causal order and freedom from deadlock by construction: nothing waits while holding a cown. Behaviours start as soon as they are runnable, while `main` is still running. The process exits when `main` has returned and no behaviour is queued or running.
- **Threads (D67).** `checkers run --threads N` (default: the number of cores) runs behaviours on N threads: N − 1 workers from the start, and the main thread too once `main` returns. `--threads 1` is the M2 scheduler exactly: one FIFO queue after `main` returns, so output is deterministic. An executable written by `checkers build` takes its thread count from the environment variable `CHECKERS_THREADS` (default: the number of cores). Golden run tests use `--threads 1`; stress tests (`tests/stress/`) run each program 10 times on 8 threads, compare its output lines sorted (D68 allows any order between behaviours that share no cown), and fail if any two runs differ.
- **Output (D68).** Each `terminal` call is atomic: lines from behaviours that share no cown may come in any order, but never interleave within a call.
- **`par` (D69).** The components of `par (e1, …, en)` run on threads of their own, at most N − 1 at a time across the program; when none is free, the remaining components run on the current thread. The result is the same tuple either way.
- **Actors (D70).** `stdlib/actor.ck`: an `Actor s` is a cown holding state `s`, made by `actor.new init sched`; `actor.send a f sched` (with `f~(s -> s)`) schedules `when x = a using sched: f x`, so messages to one actor are handled one at a time, in the order sent. State invariants are refinement types on `s`, as for any cown (§8.5).

Cown invariants (§8.5) need no runtime support: inside `when l = log`, `l` has the cown's content type, so a refinement such as `len l <= 100` is a fact the prover uses (`examples/log.ck`).

### 13.6 Run tests

A run test is `tests/run/NAME.args`: its first line is the program to run (relative to `tests/run/`, so `../../examples/wc.ck` runs an example), and each further line is one argument. `cargo test` runs it with the `checkers` binary (`checkers run --threads 1`), the working directory `tests/run/` and standard input from `NAME.in` (empty if absent), and compares standard output, standard error and the exit code with `NAME.out`.

### 13.7 Performance

Native code (§14) is about 45× faster than the M2–M8 interpreter it replaced (D80): `wc.ck` counts a 12.7 MB file in 0.73 s, against 32.7 s (release builds, one thread, checking and compiling included); arithmetic-heavy code about 10×. Compiling costs a few milliseconds per program, also for `check` declarations and staging.

On several threads, `fib 30` written with `par` runs about 1.5× faster on 2 cores than on 1. Behaviours pay for coordination between cores, about 1.5 µs each when one thread creates them and another runs them: a fork/join tree of 65 536 behaviours that each add two numbers runs in 0.14 s on 2 threads against 0.05 s on 1 (where the FIFO queue needs no synchronisation). With about 5 µs of work per leaf the same tree is 1.35× faster on 2 threads, and with about 17 µs 1.6× faster.

## 14. Native code (M8, D72–D77)

`checkers run` compiles the program to native code in memory and runs it; `checkers build FILE.ck -o PROGRAM` writes an executable. Code is in `src/native/`, the runtime in the `checkers_rt` crate (`rt/`).

**Pipeline (D72).**

```
staged, erased code (src/run/ir.rs)
  │ closure conversion (lower.rs): every lambda becomes a function taking its closure and arguments
  │ reference counting (rc.rs): dup, drop and reuse inserted (D74)
  ▼
first-order code ──codegen.rs──▶ Cranelift IR ──┬──▶ in memory (JIT): `checkers run`
                                                └──▶ object file + libcheckers_rt.a ──cc──▶ `checkers build`
```

**Values (D73).** A value is one 64-bit word: `2n + 1` for an integer `n` that fits in 63 bits; `0` for an erased value; `8k + 2` for constructor `k` without fields; `8k + 4` for unit and the capabilities; otherwise a pointer to a heap object. An object is a header (reference count; kind, field count and constructor or arity) followed by its words. Closures hold a code pointer and their free variables; a partial application holds the function and the arguments so far. Strings and bytes hold their bytes. Numbers that don't fit, decimals, bags, files, cowns and futures are Rust values behind an object. Literals and the closures of definitions are static data that is never freed. Addition, subtraction, multiplication and comparisons of small integers, equality of small integers, byte indexing, and calls of closures of the right arity are inline; the rest calls the runtime. **Not yet:** leaving out the overflow check where a refinement bounds a number (`U8`); it changes no result.

**Memory (D74).** Functions receive their arguments owned and consume them. Each variable a function binds goes to the last part of an expression that uses it; earlier parts borrow it, and a borrowed variable is duplicated only where it is kept (returned, stored, passed on). Primitives and builtins borrow their arguments. A `match` duplicates the fields its arm uses; if the arm doesn't use the value matched on, it is dropped, and if the arm builds a constructor with as many fields, the drop becomes a *reuse*: when it was the only reference, the new value is built in its memory. Counts are atomic. Constants (definitions without parameters) are computed on first use and kept for good. `CHECKERS_RC_CHECK=1` counts the objects left at exit (only constants' values should remain); `CHECKERS_NATIVE_DUMP=1` prints the first-order code with its reference counting.

**Calls (D75).** Every function uses Cranelift's `tail` convention; calls in tail position are `return_call` or `return_call_indirect`, so tail recursion runs in constant stack. Code runs on threads with large stacks (1 GiB for `main`, 256 MiB for workers). The runtime calls compiled code through a generated trampoline, `ck_invoke`.

**Runtime.** `checkers_rt`: allocation and freeing, big integers (`rt/src/num.rs`), the `__builtin`s of `stdlib/` (`rt/src/builtins.rs`), `format` and `==`, I/O with atomic terminal calls (D68), behaviours and `par`, the scheduler, and runtime errors (``runtime error in `f`: …``, exit code 70). Native code describes its constructors and definitions to the runtime in a short text descriptor. `checkers build` links with `libcheckers_rt.a`: the one named by `CHECKERS_RT_LIB`, else the newest next to the `checkers` executable or in `deps/` beside it.

**Scheduler (D77).** `rt/src/sched.rs`: Verona's per-resource queues with atomic links (§13.5), runnable behaviours on a lock-free queue (Vyukov's bounded multi-producer, multi-consumer queue, with a locked overflow), a worker running next the behaviour its own completion made runnable, and idle workers polling briefly before they sleep. A behaviour keeps the cells it names until it has released them.

**Compile-time evaluation (D80).** `src/native/eval.rs` keeps one in-memory module per checked program: each `check`, and each value staging computes, is compiled as a function of no arguments and added to it, with the definitions it needs (each compiled once), then run on a thread of its own. A runtime error there doesn't exit: the runtime reports it to the waiting compiler, which turns it into a diagnostic (E0261 for a `check`, E0273 in staging), and the stopped thread is left parked. The result is read back from its words: for staging into a term (numbers, strings, bytes, constructors, tuples; a function has no term, so its call stays at run time), for a failed `check` into the text `format` would give.

**Tests.** The golden runner runs each `tests/run/` case with the `checkers` binary; each stress case 10 times on 8 threads; and it builds two programs with `checkers build` and runs the executables.

**Dependencies.** `cranelift-codegen`, `cranelift-frontend`, `cranelift-module`, `cranelift-jit`, `cranelift-object`, `cranelift-native` 0.137 (all from the Bytecode Alliance, pure Rust; D5) and `target-lexicon`.
