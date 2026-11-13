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
| D3 | `Prop` is a definitionally proof-irrelevant, impredicative universe (as in Lean 4). | 11/05/2026 | withdrawn (11/11/2026): superseded by D124 |
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
| D15 | **Interfaces** (type classes, Lean-style instance resolution) provide `==`, `<`, `+`, `format`, etc. Needed for D0's own example (`format x + y`). Detailed design deferred to its own section; until then the prelude's operators are built in. | 11/05/2026 | **(proposed, open)**; deferred (11/12/2026): not needed for now, operators stay built in (D38, D125) |
| D16 | **Abstract type constructors declare parameter polarity** (`export abstract record Map k +v`). `+v`: `v` occurs only strictly positively (never to the left of an `->`), so the type is covariant in `v` and may hold the type being defined (a `Json` containing `Map String Json`). `-v`: `v` occurs only negatively, so the type is contravariant in `v`. Unmarked: no promise, so invariant, and a recursive type may not occur there. The defining module checks each mark against the constructors (E0359); importers rely on the marks, for strict positivity and for variance (D71). Marks are only for abstract types (E0360): other types' polarity is worked out from their constructors, where a parameter counts as positive only if it is strictly positive. In the standard library, `Future +a`; `Cown a` is unmarked, so invariant. | 11/05/2026 (rev. 11/06/2026) | decided (11/06/2026) |
| D17 | `match` is first-match. Each arm sees the negations of earlier arms' patterns and guards as hypotheses. | 11/05/2026 | decided (11/06/2026) |
| D18 | `==` inside constraints, `ensures`, and `check` is propositional equality and works on any type. In runtime code, `==` requires an `Eq` instance (D15), derived automatically for enums and records whose fields have one. | 11/05/2026 | withdrawn (11/12/2026): superseded by D125 |
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
| D47 | **Permutations are multiset equality.** The prelude-level module `bag` provides `Bag` (a finite multiset of `Int`) with `bag.of xs`, `bag.count x b`; `list.perm xs ys` is `bag.of xs == bag.of ys`. The prover maps `Bag` to Z3 arrays `Int → Int`, so permutation facts are decidable without quantifiers (as Liquid Haskell does with its `Bag` measure). Generalised by D138 (f): `Bag a` for any element type, `a → Int` in Z3. | 11/05/2026 | decided (11/05/2026) |
| D48 | **An obligation the prover can't discharge is an error**: E0450 (Z3 found a counterexample or gave up), E0451 (outside the SMT fragment, §7.3). The message shows the goal, the facts in scope and the counterexample. Examples that need a later milestone are listed in `examples/PENDING` with their expected output under `tests/pending/`; `checkers run --unverified` runs a program whose only errors are unproven obligations, keeping the runtime checks of §13.3. | 11/05/2026 | decided (11/05/2026); `examples/PENDING` and `tests/pending/` removed (11/12/2026): no example waits on a milestone, so every example must check clean |
| D49 | **Proof statements (D13).** `have e`: if `e` applies a lemma, its preconditions become obligations and its `ensures` a fact; otherwise `e` is a `Bool` that is proven, then becomes a fact. `auto` proves the current goal from the facts in scope; `admit` assumes it (trust ledger). `have` may also appear in function bodies. A lemma that uses itself is an induction and must recurse structurally, like a function. | 11/05/2026 | decided (11/05/2026) |
| D50 | **Calls assume the callee's postcondition**, including recursive calls, which is how induction over a function's own recursion works (as in Dafny and Liquid Haskell). This is sound because total functions terminate (structural recursion, or a `decreasing` measure proven to decrease, D55). | 11/05/2026 | decided (11/05/2026) |
| D51 | **A function with a precondition must be called with all its arguments** (E0453): a partial application would hide the call where the precondition is checked. | 11/05/2026 | decided (11/06/2026), relaxed by D52, lifted by D86 |
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
| D82 | **Refined types can be written inside types (M10, §7.5).** In a type, a parenthesized constraint list is a refinement type: `xs~List (n~Int, n >= 5)`. A function type may name its parameter and result and constrain them: `f~(x~Int -> y~Int, x >= 5, y > x)`, where predicates that mention only parameters are preconditions and the others postconditions. An unnamed side stays plain: `(x~Int -> Int, x >= 5)`. Each is an anonymous refinement alias, so everything D71 says about aliases holds for it. | 11/06/2026 | decided (11/06/2026) |
| D83 | **Weakening a refinement is a proof obligation, not a type error (§7.5).** Where D71 compares a found and an expected refinement in a covariant position (a type argument, a function's result), the found one may be stronger: `List (n~Int, n >= 6)` passes as `List (n~Int, n >= 5)` when the prover shows `n >= 6 ⇒ n >= 5` for any `n`. That is first-order (no induction: it is about one element), so it is an obligation (E0450) with a counterexample. A contravariant position (a function's parameter) flips it. Gaining a refinement where the found type has none (`List Int` as `List Big`) stays E0262 (D71c). Two refinements are compared by implication, not by name: `Big` and `(n~Int, n >= 5)` are the same type. | 11/06/2026 | decided (11/06/2026) |
| D84 | **Calls of function-typed values (§7.5).** Calling `f a` where `f~(x~A -> y~B, P x, Q x y)` obliges `P a` (as D71 already does for an alias parameter) and gives the fact `Q a (f a)`, so the result is known to satisfy the function type's postcondition. The prover keeps `f` uninterpreted (§7.3) and adds the fact at each call. | 11/06/2026 | decided (11/06/2026) |
| D85 | **Passing a function where a refined function type is expected (§7.5).** A named function, a partial application or a lambda passed where `(x~A -> y~B, P x, Q x y)` is expected is checked against it: the expected precondition must imply the function's own (`P x ⇒ pre x`, contravariant), and its own postcondition must imply the expected one (`P x ∧ post x y ⇒ Q x y`). Both are obligations (E0450) at the place it is passed, reported as "`list.map` may call `at_least 7` with any `x` where `x >= 5`, but it needs `x >= 7`", with a counterexample. A lambda's body is checked with `P x` as a fact and `Q x y` as an obligation on its result, as D71 already does for aliases. A function type with no predicates is the weakest expectation: passing a function with a precondition there fails with a counterexample. | 11/06/2026 | decided (11/06/2026) |
| D86 | **Partial applications are allowed everywhere; E0453 is retired (lifts D51).** `at_least 5` has the refined function type `(x~Int -> y~Int, x >= 5)`: the remaining parameters, with the supplied arguments put into the preconditions and postconditions. Where it is passed, D85 checks it; where it is called, D84. So `list.map (at_least 5) xs` checks when every element of `xs` is known to be at least 5. The failure E0453 reported becomes a D85 obligation with a counterexample. E0453 is not reused. | 11/06/2026 | decided (11/06/2026) |
| D87 | **Function arguments are typed before the function is (§7.5).** For a call like `list.map sub5 xs`, the elaborator takes the type of `xs` before checking `sub5` against `(a -> b)` (as it already does for a lambda, D71), so `a` is `Big` and D85 can see the promise `xs` makes. Without this, the order of arguments would decide whether a program checks. | 11/06/2026 | decided (11/06/2026) |
| D88 | **Tools written in Checkers ship inside `checkers` (§15.1).** Their source lives in `tools/` and is embedded in the binary like the standard library. `checkers fmt …` and `checkers lsp …` run the tool's `main` with the remaining arguments. A tool is proven by `cargo test` (it must check with zero diagnostics, like `examples/`), not each time it starts. The build compiles each tool to native code linked into `checkers`, so starting one costs no elaboration or code generation. While a tool is being written, `checkers run tools/fmt.ck …` runs the same program. | 11/06/2026 | superseded by D95 (11/10/2026) |
| D89 | **The `Toolchain` capability (§15.2).** A program run by `checkers` (a bundled tool, or `checkers run`) may take a third parameter `tc~Toolchain` in `main`. It gives in-process access to the compiler: check a file with unsaved buffers taking the place of files on disk, with or without the prover, and get its diagnostics as values. `checkers build` rejects such a `main` with a new error code, because an executable doesn't contain the compiler. | 11/06/2026 | superseded by D97 (11/10/2026) |
| D90 | **Standard library additions the tools need (§15.3).** For M11: writing to standard output without a newline; listing a directory; joining many strings in linear time; slicing bytes; checking that bytes are UTF-8; running a program with the caller's standard streams (`proc.exec`); reading environment variables and the executable's path (`env.get`, `env.executable`). For the language server (M13): reading exactly *n* bytes from standard input, `proc.run`, parsing a `Nat`, `json` in the standard library. | 11/06/2026 | decided (11/10/2026) |
| D91 | **One formatting style, with no options (§15.4).** `checkers fmt` has no configuration. Its output parses to the same tree as its input, and formatting it again changes nothing. A file with a syntax error is left alone and the error is reported. Comments, literals as written (`0x20`, `1_000`) and line breaks within a logical line are kept. There is no line-width limit, so the formatter never adds or removes line breaks inside a logical line. | 11/06/2026 | decided (11/10/2026) |
| D92 | **Formatting rules (§15.4):** 4 spaces per block level; continuation lines line up with the first item after the opening bracket or the signature's `:`, as in `examples/`; single spaces around binary operators, `->`, `<-`, `=` and after `,`, none around `~` or inside brackets; gofmt-style alignment of the arms' `->` in a `match`, the constructors' `:` in an `enum`, and trailing comments on consecutive lines (at the furthest column their author used, so aligned code keeps its layout); at most one blank line in a row, none at the start or end of a block. | 11/06/2026 | decided (11/10/2026) |
| D93 | **The formatter parses Checkers itself (§15.4).** It is written in Checkers, with its own lexer and parser that keep comments and blank lines (a concrete syntax tree). It does not get the Rust parser's tree, which drops comments. A test runs it over every `.ck` file in the repository and requires `ckc parse` to give the same output before and after, so the two parsers can't drift apart. | 11/06/2026 | decided (11/10/2026) |
| D94 | **LSP, first version (§15.5), deferred to M13 by D98.** Full-document sync. Diagnostics come from the compiler (`ckc check --json`, D97), run in a behaviour so that requests are still answered while it works: without the prover when a document changes (the unsaved text on standard input), with it when the document is saved; results for an older version of the document are dropped. Formatting calls the formatter's module directly, and document symbols come from its syntax tree. Positions are UTF-16 code units (the protocol's default, and the only encoding VS Code's client supports), or UTF-8 when the client offers it. Hover, go to definition and completion need queries into the elaborator and come later. | 11/06/2026 | superseded by D120 (11/11/2026) |
| D95 | **A compiler and a build tool, like `rustc` and `cargo` (§15.1).** The compiler is written in Rust and built by Cargo with no special cases. The build tool, the command people use, is a Checkers program compiled by the compiler; the formatter and the language server are part of it, as Checkers modules. Supersedes D88, which compiled Checkers tools into the Rust binary. | 11/10/2026 | decided (11/10/2026) |
| D96 | **Names (§15.1).** The compiler is `ckc`; the build tool is `checkers`. `checkers check`, `run`, `build`, `parse`, `stage` and `trust` pass their arguments to `ckc`; `checkers fmt` and `checkers lsp` are the build tool's own. The build tool finds the compiler through `CKC`, else next to its own executable, else on `PATH`. | 11/10/2026 | decided (11/10/2026) |
| D97 | **The build tool runs the compiler as a process (§15.2).** `checkers check FILE` runs `ckc check FILE` with the build tool's standard streams and returns its exit code (`proc.exec`, the first operation of the `Proc` authority); the same for the other compiler commands. A machine-readable interface (JSON diagnostics, overlays for unsaved files, an index for go to definition) waits for the language server (§15.5). Supersedes D89, which gave tools the compiler in process. | 11/10/2026 | decided (11/10/2026) |
| D98 | **Scope and order of the tools work (§10, §15).** M11 is the build tool and the formatter only. M12 makes checking and building faster, including incremental compilation. The language server is M13 (moved to M15 by D103–D109). | 11/10/2026 | decided (11/10/2026) |
| D99 | **Formatter details found while building it (§15.4).** (a) A trailing comment's column is the furthest, over its run, of each line's code end plus the spaces its author put before the comment (at least two), rather than the column it was at: aligned comments stay aligned when the code moves (re-indented, respaced). (b) Inside `{ }` one space at each end (`System { fs, term }`, as `examples/` writes it), not none as in `( )` and `[ ]`. (c) A type's polarity marks stay glued (`record Box +v`). (d) The formatter's parser is a lexer plus the layout pass (§9.1): lines grouped into logical lines and blocks; it has no expression grammar, so it refuses lexical and layout errors (a tab in indentation, an unterminated literal, an inconsistent dedent) but formats a file with other syntax errors, keeping every token; `checkers check` reports those. (e) A match arm with a guard (`Some b if b < 0x20 ->`) is left out of its arms' alignment. (f) A continuation line outside brackets, other than a signature's, keeps the indentation its author gave it relative to the line it continues, at least one level (`hex4` in `stdlib/json.ck`). | 11/10/2026 | decided (11/10/2026) |
| D100 | **Z3's answers are cached (M12).** Each answer (proved, a counterexample, or gave up) is stored under the exact SMT-LIB query given to Z3, together with Z3's version; checking again with the same query and the same Z3 reuses it without running Z3. The query includes everything the obligation depends on (definitions, facts, the goal, Z3's options), and with D101 Z3's answer depends on nothing else, so the stored answer is the one Z3 would give; a change anywhere the obligation reads gives a different query and a new answer. What is stored is Z3's output; diagnostics (spans, messages, the counterexample as shown) are built from it each time, so moved code and newer messages show. The cache lives in `.checkers/` beside the checked file's module root; each entry keeps the full query, compared in full on a hit, so a hash collision can't reuse a wrong answer. `ckc check --no-cache` ignores it; `ckc trust` says how many answers came from it. | 11/10/2026 | decided (11/10/2026) |
| D101 | **Z3 is limited by work, not time (M12).** Queries set Z3's resource limit (`rlimit`) instead of a 10-second timeout, so whether an obligation is proved no longer depends on the machine or its load: the same query gives the same answer everywhere. The limit is chosen from measurements so that every obligation in the repository passes with a margin. | 11/10/2026 | decided (11/10/2026) |
| D102 | **Elaborated modules are not cached yet (M12).** Type checking every module of `examples/json.ck`, the standard library included, takes about 30 ms, under 1% of checking it; proving takes the rest. Caching elaborated modules (serializing core terms and the global tables) waits until elaboration of a program takes over 1 s. | 11/10/2026 | decided (11/10/2026) |
| D103 | **Three layers (§16.1).** (1) The **prelude**: the types and operators the compiler knows by name (`Nat`, `Int`, `Bytes`, `String`, `Bool`, `Option`, `Result`, `List`, tuples, the fixed-width aliases, `Char`, `len`, `++`, `==`, indexing, arithmetic, `format`), imported everywhere; a closed set, changed only by a language decision. (2) **Builtin modules**: functions the runtime implements (`__builtin`), each with its full contract in the module's `.ck` file and its code in `rt/src/builtins/<module>.rs`; their postconditions and `__builtin` lemmas are trusted and listed by `ckc trust` wherever a program uses them. (3) **Checkers modules**: everything else, written in Checkers with proofs. A function is builtin only if it needs the runtime (the OS, the scheduler), works on the representation of a primitive type (`Bytes`, `String`), or is a fact about another builtin; anything expressible in Checkers is written in Checkers. | 11/10/2026 | decided (11/10/2026) |
| D104 | **The standard library is the package `std`, shipped beside `ckc` as source (§16.1).** It is read from disk, not embedded in the binary, as Go reads `$GOROOT/src`: editing a module takes effect at the next check, with no rebuild of `ckc`. `ckc` finds it through `CHECKERS_STD`, else `../lib/checkers/std` from its own directory (an installation), else the `stdlib/` of the source tree it was built from (development builds only). Each lookup is relative to the running `ckc`, so an installed toolchain and a development build never see each other's library; if none is found, `ckc` stops with an error naming the places it looked. It differs from other packages only where it must: its version is the toolchain's (it is not in `checkers.lock`); only `std` may declare `__builtin`, and each builtin must exist in this `ckc`'s runtime (changing a builtin's contract or adding one needs the runtime, so a rebuild); and the prelude's types are the ones the compiler knows by name. Its proofs are checked like any package's (D109), with answers cached (D100). | 11/10/2026 | decided (11/10/2026; revised from: embedded in `ckc`) |
| D105 | **Module names (§16.2).** The standard library's modules are `std.…` (`import std.list`), and the prelude is `std.prelude`. An import's first component says where it comes from: `std`, a dependency named in the package manifest, or else this package's own files (D53). By default a module is referred to by the last component of its name (`import std.list` → `list.map`), as in Go; `as` renames it, and two imports with the same last component need `as`. So adding a module to the standard library never collides with a package's modules, and short qualifiers stay short. Supersedes D53's lookup order (the standard library before local files). | 11/10/2026 | decided (11/10/2026) |
| D106 | **What the standard library contains (§16.3).** Exactly the modules in the §16.3 table, each with its contents listed. A module belongs there if it (a) is needed to use a primitive type or a capability at all, (b) defines a vocabulary type that packages' interfaces exchange (`Map`, `Set`, `Array`, `Json`), or (c) is a widely used algorithm the standard library should ship with its proofs (`sort`). Anything else is a package. Adding or changing an exported function is a decision recorded here, with the table updated: no function is added only because a program needs it. | 11/10/2026 | **(proposed)**; the scope is to be settled later; until then the standard library stays small: today's modules, plus what M13–M14 need (11/10/2026) |
| D107 | **Packages (§16.4).** A package is a directory with a manifest, `checkers.json`: the package's name, version, the oldest toolchain it needs, and its dependencies. The build tool reads it with `std.json`, and reports a malformed manifest with its line and column. The lock file is `checkers.lock` (JSON as well; written by the build tool). | 11/10/2026 | decided (11/10/2026): `checkers.json` and `checkers.lock`; the lock file's format proposed |
| D108 | **Dependencies (§16.4).** A dependency is a git repository and a version (a tag `vMAJOR.MINOR.PATCH`) or a local path. Versions are chosen by minimal version selection (Go): each package states the oldest version it works with, and the build uses, for each dependency, the highest of those minimums; deterministic, no solver, and a new release upstream changes nothing until someone asks for it. `checkers.lock` records each dependency's commit, so a build is reproducible. Different major versions of one package are an error for now. There is no registry yet. The build tool fetches with `git` (`proc.exec`) into `~/.cache/checkers/packages/`. | 11/10/2026 | decided (11/10/2026) |
| D109 | **Checking with packages (§16.4).** The build tool passes `ckc` each package as `--package NAME=DIR`, with the dependencies each may import; a module may import only its own package, `std`, and the dependencies its manifest declares. A dependency's proofs are always checked, like the program's own; there is no way to trust a dependency unchecked (the answer cache, D100, makes that cheap after the first time), and `ckc trust` lists every package's admits and the builtins it relies on. Dependency code runs no code at build time (there are no build scripts; compile-time evaluation is pure) and performs no effects except through capabilities its callers pass it, so adding a dependency can't touch the machine. | 11/10/2026 | decided (11/10/2026) |
| D110 | **What M13 shows (§7.4, §16.1).** Choices made while building M13 that appear in compiler output. (a) A standard-library module's errors are reported like any module's, at `<std>/list.ck:LINE:COL`, not as internal errors, since the standard library is editable source (D104). (b) A standard-library module whose declaration doesn't match its path is E0223, as for program modules; a `__builtin` function the runtime doesn't implement is E0361, with the Rust file to add it to. (c) `ckc` exits with status 2 and lists the places it looked when it finds no standard library. (d) The standard-library modules a program loads are proven and their `check`s run with it (D109); the summary line counts only the program's own obligations, and the trust ledger gives each such module one line (`<std>/list.ck  proved   51 by smt, 1 computed`) after its `admit`s and axioms, which stay listed one by one. (e) The ledger lists, as `builtin`, each builtin reachable from `main` at run time (from every function of the program if it has none), at its declaration. (f) An unknown module beside the program gets `help: … import std.list` when the standard library has a module of that name. | 11/10/2026 | decided (11/11/2026) |
| D111 | **Packages as built (M14, §16.4).** (a) `ckc` takes `--package NAME=DIR` for each dependency and `--uses PKG=A,B` for the packages `PKG` may import (`.` is the program's own package); with no `--package`, `ckc` works as before. A package given no `--uses` imports no packages. (b) Inside a package, its own modules are declared and imported by their path in the package (`module validate`, `import validate`); other packages import them as `json_schema.validate`. Messages call the module `json_schema.validate` and its file `<json_schema>/validate.ck`, as for `<std>` (D110). (c) A dependency's key in `dependencies` must be the `name` in that package's own manifest, so a name means one package in the whole build. Importing a package that isn't a declared dependency is E0227. (d) Dependencies' modules are checked and proven with the program, and shown like the standard library's (D110 d): one ledger line per module after its `admit`s and axioms; the summary line counts the program's own package only. (e) In a directory with `checkers.json`, `checkers check|run|build|trust|stage` first resolve the dependencies, and the file defaults to `main.ck`; elsewhere they behave as before. (f) Path dependencies are relative to the manifest that names them. A git dependency is cloned with `git` into `$XDG_CACHE_HOME/checkers/packages/NAME/COMMIT` (else `~/.cache/…`) and checked out at tag `vMAJOR.MINOR.PATCH`. Minimal version selection reads the manifest of every version reached, as Go does. If `checkers.lock` already has the selected version, its commit is used, so a moved tag doesn't change a build; otherwise the tag is resolved and the lock rewritten. The lock lists every package of the build, transitive ones included, and is written only when it changes. (g) Errors: a manifest's at `checkers.json:LINE:COL`; a `toolchain` newer than this `checkers`; two major versions of one package (naming who needs each); one name for two different path or git sources. | 11/11/2026 | decided (11/11/2026; may be revisited) |
| D112 | **Streams and processes (§8.4, §16.3).** `File` is a stream type, and everything that is a file is a `File`: an open file, a pipe to or from a child process, and the standard streams, read and written with the same operations (as Haskell's `Handle` and Eio's sources and sinks). Other kinds of stream (sockets, in-memory buffers) may be types of their own, later. (a) `std.files` adds, for any `File`: `read_some n f` (at most `n` bytes, waiting for at least one; empty only at the end), `read_exactly n f` (`n` bytes, fewer only at the end), `read_rest f`, and `write_bytes b f`, each returning `(Result … IoError, File)`. (b) `std.terminal` adds `stdin term`, `stdout term` and `stderr term`, each a new `File` on that stream: handles to one stream share the runtime's buffer, and closing one closes the handle, not the stream. `print_line` and the other `Term` functions stay, as shorthands. (c) `std.proc` adds `run program args input p`: the child's standard input is `input`, and the result is `Output { code, stdout, stderr }` (the runtime writes the input and reads both outputs at once, so a child that fills a pipe can't deadlock it); and `spawn program args ss p`, where `ss~Streams` gives each of the three `Inherit`, `Pipe` or `Discard`, returning a `Spawned ss`: the `Child`, and for each stream a field whose type is computed from `ss` (`pipe_end s`: a `File` where `s` is `Pipe`, `Unit` otherwise), so a program gets exactly the files it asked for and must close each of them; `wait c` consumes the `Child` and returns its exit code. `exec` stays: `spawn` with every stream inherited, then `wait`. A `Child` and its pipes are resources (§8.4), so forgetting to wait for a child or close a pipe is a compile error. A value whose type depends on something not known where it is used (a `Spawned ss` for an unknown `ss`) counts as a resource there, since it may hold one; checked since M15. (d) Supersedes D90's `terminal.read_bytes` (now `read_exactly` on `stdin term`); `proc.run` is the one D90 planned. A working directory and environment for the child wait for a program that needs them. | 11/11/2026 | decided (11/11/2026) |
| D113 | **Blocking operations free the thread (M16, §13.8).** A behaviour (or `main`) that waits (reading a pipe or the terminal, writing to a full pipe, waiting for a child, sleeping) is parked, and its thread runs other behaviours until it can go on, as goroutines do in Go and fibers in OCaml's Eio. Nothing in the language changes: the same functions, the same types, no `async` (no function colouring). The runtime runs each behaviour on a stack of its own, taken from a pool; waits on pipes, terminals and sockets go to a poller (`epoll`, `kqueue`); calls that can't be polled (regular files, `waitpid`) run on a separate pool of threads while the behaviour is parked (Go's hand-off of blocking system calls). A parked behaviour keeps its cowns, so causal order and freedom from deadlock (§8.5) are unchanged. | 11/11/2026 | decided (11/11/2026) |
| D114 | **Order after M14 (§10).** M15 streams and processes (D112), switching every example, tool and test over and fixing the bugs found; M16 blocking operations free the thread (D113); M17 the language server (D94). | 11/11/2026 | decided (11/11/2026) |
| D115 | **Two milestones before the language server (§10).** M17 makes reflected definitions sound for `decreasing` recursion (§7.3); M18 proves `std.json`'s `admit`s and makes `--release` reject programs with `admit`s (§7.4). The language server becomes M19. | 11/11/2026 | decided (11/11/2026) |
| D116 | **Scope of M16–M18.** (a) M16 is done on Linux x86-64 (`epoll`, the x86-64 stack switch); macOS (`kqueue`) and ARM64 come later, when a machine or CI runner can test them. (b) M17 starts by looking for a program that today's encoding lets Z3 prove something false about; if none can be found, the encoding stays and M17 ends with what was tried recorded in §7.3; if one is found, proofs that rely on the old encoding are fixed as needed. (c) `--release` means only that a program with an `admit` in its transitive ledger is refused; optimisations may be added to it later. | 11/11/2026 | decided (11/11/2026) |
| D117 | **How M16 parks (§13.8).** (a) `main` runs on its own thread, which isn't a worker until `main` returns, so its waits block only that thread (superseded by D123: `main` is a behaviour on a fiber). (b) Standard input, output and error stay blocking: making them non-blocking would change them for every process sharing the terminal (Go avoids it too). Reading standard input runs on the blocking pool while the behaviour is parked, under a lock that parks a second reader rather than blocking its thread; writing standard output or error blocks the writer's thread, because a behaviour parked while holding the output lock could leave every worker waiting for it. (c) Files on disk are read and written through a 64 KiB buffer whose system calls go to the blocking pool, so a behaviour reading line by line hands off once per 64 KiB, not per line; `files.read`, `write`, `list`, `open`, `create`, `proc.exec`, `proc.run` and `proc.wait` hand off once per call. Our ends of a child's pipes are non-blocking and wait in the poller. (d) Standard output is flushed whenever the scheduler has nothing to run and must wait, so a program waiting for input has shown what it wrote. (e) With one thread, a behaviour that parks keeps its cowns: later behaviours on any of them are held back, in order, until it finishes (the pool's queues already do this). (f) The blocking pool starts a thread whenever every thread is busy, and a thread idle for 10 s ends. Its jobs run runtime code only, never compiled code. | 11/11/2026 | **(proposed)** |
| D118 | **Reflected definitions and well-formed specifications (M17, §7.3).** What M17 found: no program led Z3 to prove something false, but the gap was real. Given as a quantified axiom, `half`'s equation (`half x = if x == 1 then 0 else 1 + half (x / 2)`, precondition `x >= 1`) makes Z3 prove anything at once, since at 0 it says `half 0 = 1 + half 0`; as `define-fun-rec` Z3 answers `unknown` instead, and a ground `half 0` makes it expand forever (4.5 minutes and gigabytes before failing). And such terms could reach Z3, because calls in specifications weren't checked. So: (a) A call in a precondition, postcondition, refinement or `ensures` must meet its callee's precondition (E0450, as in a body); each condition of a signature may rely on those before it, and a lemma's conclusion on its hypotheses. (b) A definition recursing by `decreasing` is given to Z3 only where its recursion is known to end: `f x = if D then body else f#outside x`, with `f#outside` unknown. `D` is its `Nat` parameters being non-negative and, unless its termination obligations all hold without them, its preconditions (checked once per function while proving). Structural recursion ends on every value Z3 can build and is unguarded. (c) This changes the encoding although no false proof was found (D116 b said it would stay): it removes the hang and the reliance on Z3's incompleteness, and proving got faster (8.7 s → 7.6 s for the examples, tools and standard library; no proof changed). | 11/11/2026 | **(proposed)** |
| D119 | **Characters and strings in proofs (M18, §7.3, §16.3).** To prove `std.json`'s string round trip without `admit`s: (a) `std.char`'s `code`, `from_scalar`, `from_ascii` and `from_surrogates` become Checkers functions instead of builtins (a `Char` is its scalar value, so each is the identity or the surrogate formula), and the prover sees through them. (b) `std.string` gains `chars s`, a string's characters in order. (c) New axioms (D56): `string.from_chars_nil`, `from_chars_cons`, `from_chars_chars` (`from_chars (chars s) == s`), `concat_map_chars` (`concat_map f s` is `f` mapped over `chars s`, joined), `from_char_bytes` (a character's UTF-8 bytes: one byte, its code, if it is ASCII; otherwise starting at 0xC2 or above) and `utf8.decode_from_char` (decoding a character's own bytes gives it back, whatever surrounds them). `check`s in each module compare them with the builtins on sample characters. (d) `std.list` gains four proven lemmas: `keys_append`, `contains_append`, `contains_reverse` and `unique_split`. | 11/11/2026 | **(proposed)** |
| D120 | **The language server, first version (M19, §15.5).** Supersedes D94. Decided: (a) proofs run on every change, as types do; there is no on-save mode. (b) Hover and semantic highlighting are in the first version, with diagnostics, go to definition, formatting and document symbols. (c) The client it is built and tested for is Eglot (Emacs); the repository ships the server only, no editor mode. Proposed: (d) `checkers lsp`, in the build tool (D95), runs `ckc check --json --overlay FILE` as a child process for each check; a newer version of any open document kills the check in progress, so there is no delay timer: a check starts at once and the next edit cancels it. (e) `--json` writes JSON lines in three phases, each ended by a `done` line: syntax, names and types (with the index), then `check`s, then proofs. The server publishes the diagnostics it has after each phase, so type errors don't wait for Z3. (f) `--overlay FILE` names a JSON object mapping paths to the text that stands in for them, applied where the compiler reads files (as `go build -overlay`). (g) The index has each name in the file being checked with its definition, kind and type (for go to definition, hover and highlighting) and each keyword, comment, string and number (for highlighting). (h) `proc.kill` ends a child process. (i) Positions are UTF-8 when the client offers it, else UTF-16. (j) Measured, from the edit to its diagnostics: type errors under 100 ms on `tools/checkers.ck`. (k) Withdrawn (11/11/2026): the workaround is removed, since `main` is a behaviour on its own fiber (D123). It was: found while building it, the server's loop runs in a `fork`, and `checkers`'s `main` returns a `Future ExitCode` (D31), because `main` holds its thread until it returns (D67): with one thread (`CHECKERS_THREADS=1`, or one core) a server looping in `main` would never let a check's behaviours run. (l) `files.flush`: a reply goes out when it is written, not when the scheduler next idles (D117 d). (m) `proc.killer c` gives a `Killer` for a `Child` that is not itself a resource, so the main loop can end a check that a behaviour is reading; `proc.kill` sends SIGKILL unless the child has been waited for (it is reaped only under the lock `kill` takes, so a reused process id is never signalled). | 11/11/2026 | (a)–(c) decided (11/11/2026); (d)–(m) **(proposed)** |
| D121 | **`Nat` is a refinement of `Int` (§3, D6, D38).** `type Nat = n~Int, n >= 0` in the prelude, as in F\* and Dafny. (a) A `Nat` is an `Int`: passing one where an `Int` is expected is free (D71 b), also inside types (`List Nat` as `List Int`), and `Nat` and `Int` operands mix. (b) An `Int` where a `Nat` is expected is a proof obligation, `n >= 0` (E0450), not a type error. (c) `+`, `*`, `/` and `%` of `Nat`s are `Nat`s without an obligation; `-` of `Nat`s keeps its obligation `a >= b` (D6). (d) Fixed-width types are unchanged (`U8 = n~Nat, n < 256`). (e) Nothing changes at run time (D73) or in the prover, which already reads `Nat` as `Int` with `n >= 0`. Proving time is measured before and after: checking every example, `tools/checkers.ck` and all of `std` with no cache takes about 31 s either way, and `tools/checkers.ck` has the same 347 obligations. | 11/11/2026 | decided (11/11/2026) |
| D122 | **Check as far as possible past errors (§12).** (a) After a syntax error, every declaration the parser recovered is still type-checked; a use of a declaration that failed sees its signature, or nothing if that failed too. (b) Obligations are proven for every declaration without errors whose obligation mentions nothing that failed to elaborate; a declaration with errors gets none. (c) Each `check` runs if its expression has no errors and nothing it uses has errors. The editor (§15.5) shows type errors and the other declarations' proofs together. | 11/11/2026 | decided (11/11/2026) |
| D123 | **`main` runs on a fiber like any behaviour (§13.8).** Supersedes D117 (a): when `main` waits (reading standard input, a pipe, a child) it parks and its thread runs other behaviours, so a program looping in `main` (a server, a REPL) works on one thread. The N threads of D67 are N workers; `main` is the first thing they run. | 11/11/2026 | decided (11/11/2026) |
| D124 | **No `Prop` (withdraws D3).** Nothing in the language needs a universe of propositions: every predicate (precondition, postcondition, refinement, invariant, `ensures`, lemma) is a `Bool` expression, Z3 proves it, and erasure comes from multiplicity 0, not from a universe. In the core calculus (§3) a proof that `φ : Bool` holds has type `Holds φ`, whose one inhabitant is `smt_trusted φ`; a binder of type `Holds φ` is forced to multiplicity 0. Impredicativity, `t = u` and `refl` go with `Prop`: no surface syntax could write them. If certificate checking (D1) one day needs proof terms, they are added then. | 11/11/2026 | decided (11/11/2026) |
| D125 | **`==` never compares functions.** (a) `==` and `!=` on a function type, or on a type that contains one (a field, a constructor argument, a tuple component, a type argument), are a type error (E0263), where the comparison is compiled: function bodies and `check`s. In specifications (refinements, invariants, preconditions, `ensures`, lemmas) `==` is logical equality and works on any type. (b) The same holds through type parameters: a function that compares values of its type parameter `a` with `==`, itself or through a function it calls with `a`, can't be called with `a` a function type or one containing it (E0264). This is the rule (a) applied to generic code, so a comparison of functions never reaches the runtime. (c) Capabilities (`Sched`, `Fs`, `Env`, `Proc`, `Net`, `Clock`, `Term`), cowns, futures, files and process handles (`Child`, `Killer`) are treated as functions are: no equality, a type error by (a) and (b). Of the built-in types, only `Int` (and its refinements), `String`, `Bytes`, `Bag`, `Decimal` and `IoError` compare. | 11/12/2026 | decided (11/12/2026); (c) 11/12/2026 |
| D126 | **macOS on ARM64 (Apple silicon) is supported, alongside Linux on x86-64** (D116 a's "later"). Everything builds and runs on both: `ckc` (check, prove, `run`, `build`), the runtime, and `checkers`; the whole test suite passes on both. Platform code is chosen at compile time: the fiber switch (x86-64 System V or ARM64 AAPCS64), the poller (`epoll` or `kqueue`), and the system libraries an executable links with. Linux on ARM64 uses the same ARM64 switch, but no machine tests it yet. | 11/12/2026 | decided (11/12/2026) |
| D127 | **The language server, as used (Eglot).** Decided (Ian's report, 11/12/2026): (a) find references; (b) highlighting follows the text as it is typed, and shows when a file is opened. Proposed, how: (c) a request about a file (highlighting, hover, definition, references, outline) is answered from the index of that file's latest check: if that check hasn't given its index yet, the answer waits for it. A client fixes each answer to the version of the text it asked about (Eglot paints the tokens it gets onto that version and doesn't ask again until the next edit), so an answer from an older check paints the old positions onto the new text, and an empty one at open leaves the file unhighlighted. (d) The index is a phase of its own in `--json`, ended by `{"kind":"done","phase":"index"}`, so the server has it as soon as it is written, without waiting for the `check`s. (e) A change kills only a check of the same file (D120 d killed any check in progress), so every open file's latest check finishes and its waiting requests are answered. (f) References are found in the indexes of the open files: each name whose definition is the one under the cursor (and the definition itself when the client asks for it). | 11/12/2026 | (a), (b) decided (11/12/2026); (c)–(f) **(proposed)** |
| D128 | **Hover shows a declaration's description.** Decided (Ian, 11/12/2026): hovering over a name shows its signature and its description, as other language servers do. Proposed: (a) a declaration's description is the run of `#` comment lines directly above it (no blank line between), as the standard library and the tools already write them; a field's or a constructor's is the one above its line. The `#` and one space are removed from each line, and the text is shown as Markdown. (b) In `--json`, a `name` line carries it as `"doc"` (a string, or `null` when there is none). | 11/12/2026 | decided (11/12/2026); (a), (b) **(proposed)** |
| D129 | **CI and releases (v0.0.1).** Decided (Ian, 11/12/2026): (a) pull requests merge through a merge queue that runs the whole test suite on every supported platform (Linux x86-64 and macOS ARM64, D126); (b) every pull request runs the tests that aren't integration tests; (c) CI caches as much as it can, above all the Z3 built from source; (d) releases are immutable. Proposed, how (`.github/workflows/`): (e) one job per platform for pull requests, the merge queue and `main`, so the checks a branch rule requires have the same names in each: clippy (`-D warnings`) and the unit tests always, the integration tests (`cargo test --tests`: golden files, packages, parking, the standard library, the cache) in the merge queue and on `main`. (f) `Swatinem/rust-cache` keeps `~/.cargo` and the dependencies' build output, the Z3 build included; one cache per platform, saved only by `main`, restored by pull requests and the merge queue. (g) The Rust toolchain is pinned (1.98.0) and every action by commit. (h) A tag `vX.Y.Z` must match `Cargo.toml`'s version; the release workflow tests that commit on each platform, packages `bin/ckc`, `bin/checkers` and `lib/checkers/std` (where `ckc` looks for the standard library, D104) as `checkers-vX.Y.Z-TARGET.tar.gz` with its SHA-256, attests the archives' provenance, creates the release as a draft, attaches them, then publishes it. (i) In the repository's settings, by hand: turn on immutable releases (publishing then locks the tag and the archives), a merge queue for `main` requiring `test (ubuntu-24.04)` and `test (macos-15)`, and a rule protecting `v*` tags. | 11/12/2026 | (a)–(d) decided (11/12/2026); (e)–(i) **(proposed)** |
| D130 | **What is trusted, as built (§1).** There is no kernel: §1 said one re-checks the elaborator's core terms, so that the parser and elaborator need not be trusted, but none was built. §1 now names the trusted parts: parser and elaborator (types, refinements, exhaustiveness, usage, termination, obligations), the SMT translation and Z3, the code generator and runtime (which also prove facts by evaluation), and the standard library's axioms and builtins' signatures. An independent kernel is later work. Found by the v0.0.1 soundness review (11/12/2026), which found no unsoundness: division and remainder agree between Z3 and native code, a `partial` function's postcondition can't be used to prove a falsehood, non-structural recursion without `decreasing` is rejected, and `--unverified` programs keep their run-time guards. | 11/12/2026 | decided (11/12/2026) |
| D131 | **Documentation and the language's site (§15.6).** Decided (Ian, 11/12/2026): (a) package documentation like `godoc`, the standard library's included, generated by `checkers` (in Checkers), every page as HTML and as Markdown (for agents); (b) a site explaining the language, the same way; (c) versioned documentation: each release's stays as it was published, `main`'s follows `main`; (d) documentation of any package from its git repository, as pkg.go.dev does, waits for hosting that can run a server: GitHub Pages serves only files built in advance. Proposed, how: (e) `ckc doc FILE` writes a module's exported declarations as JSON lines, from the syntax tree only (a module with type errors still has documentation). (f) `checkers doc DIR -o OUT [--name NAME] [--root PATH] [--label TEXT]` documents the package in `DIR` (every `.ck` file in it, recursively): `OUT/NAME/index` (its modules, each with the first sentence of its description) and `OUT/NAME/MODULE` (its declarations), each as `.md` and `.html`; the Markdown is written first and the HTML rendered from it, so they say the same. (g) `checkers site SRC -o OUT` renders each `SRC/*.md` page to `OUT` as `.md` and `.html`, and writes `OUT/llms.txt` (llmstxt.org) listing the pages and the latest documentation. (h) HTML comes from a subset of Markdown (headings, paragraphs, lists, fenced code, tables, links, emphasis, inline code) rendered by `tools/ck/markdown.ck`; `checkers` code blocks are highlighted; each HTML page names its Markdown twin (`<link rel="alternate" type="text/markdown">`). (i) Hosting: GitHub Pages, deployed by Actions when CI passes on `main` and when a release is published, with the binaries CI built for `main`'s latest passing commit (Pages builds nothing): the site and `dev` always come from that commit, and a release's deploy only adds its documentation. Documentation by version (Ian, 11/13/2026): `/docs/dev/` is `main`; `/docs/vX.Y.Z/` each release, unpacked from the archive `checkers-vX.Y.Z-docs.tar.gz` that the release workflow built with that tag's own tools and attached to the (immutable) release; `/docs/latest/` a copy of the highest release, or of `dev` before the first. Nothing generated is kept in the repository. (j) `std.files.create_dirs` creates a directory and its parents. (k) Every export of `std` has a description. (l) Decided (Ian, 11/13/2026): pages show no link to `llms.txt` or to their Markdown twin, and name both in `<link>`s; the top bar's Documentation is always the latest; the version is a menu of the others; links within documentation stay within its version; a module's page has a navigation column listing its declarations, headed by `package.module` whose `package` leads back; every type in a signature is a link. Proposed, how: (m) the version menu reads `/docs/versions.json`; names in signatures resolve as the compiler resolves them, only to the documented package; a package's `README.md` is its page's description, and a module's description stays the comment that opens its file. | 11/12/2026 | (a)–(d) decided (11/12/2026), (l) decided (11/13/2026); (e)–(k), (m) **(proposed)** |
| D132 | **`Type` is declared in the prelude (§9.5).** `export abstract enum Type` in `stdlib/prelude.ck`, like `Int`, so the type of types has a declaration, a description and a place in the documentation: every `Type` in a signature links to it (§15.6), and `ckc check --json` gives it as `Type`'s definition and description, for hover and go to definition (§15.5). The compiler binds that declaration to the universe (`Type ℓ`, §2) rather than making a new type; nothing else about `Type` changes. It is in the prelude, not a module of its own, because only the prelude is in scope in every module. Decided (Ian, 11/13/2026): `Type` declared in `std` like the other built-in types; proposed: in the prelude. | 11/13/2026 | decided (11/13/2026), its place in the prelude **(proposed)** |
| D133 | **Arrays, with packed elements (M21, §9.5, §14, §16.3).** Decided (Ian, 11/13/2026): `Array a` ships on the current one-word representation, without monomorphising; arrays of fixed-width numbers are packed, every width, not only bytes; `Bytes` is `Array U8`. Proposed, how: (a) **Type.** `export abstract enum Array +a : a~Type` in the prelude: immutable, with `len` and indexing in O(1). `export type Bytes = b~Array U8`, so `b"…"`, the bytes builtins and everything typed `Bytes` are arrays of `U8`, unchanged for programs. (b) **Operators.** `len a`, `a[i]` (of type `a`'s element type, obliging `i < len a`), `a ++ b`, and `==` element by element (when the elements compare, D125). (c) **`std.array`.** `from_list`, `to_list`, `repeat`, `init` (element `i` is `f i`), `map`, `set` (a new array with one element replaced: in place when the array isn't shared, else a copy, D74), `slice`, `concat`, `reverse`, `all`, `contains`, `count`, `take`, `drop`, each with its postconditions. `init` and `map` are builtins that call the function for each element and write the result straight into the new array (one allocation, no list). (d) **Prover.** `Array a` is `(Seq S)` for `a`'s sort `S`, `len`, indexing and `++` native, as for `Bytes` today; the element type's refinement is assumed of each `a[i]` (for `U8`, `0 <= a[i] < 256`, as now). (e) **Layout.** An array object's header says how its elements are stored: one word each (as for every other value, D73), or packed: 1 byte (`U8`, `I8`, `Bool`), 2 (`U16`), 4 (`U32`, `I32`, `Char`) or 8 (`U64`, `I64`), signed or not. The layout comes from the element type's name, after unfolding aliases; other refinements don't change it. Reading (`len`, indexing, `==`, `format`, slicing, the builtins) goes by the header. A packed `U64` or `I64` element that doesn't fit a 63-bit word is read as a big integer. (f) **Creating.** An array built from elements (`from_list`, `repeat`, `init`, `map`, `concat`, literals) is laid out for its element type where it is created. One made from other arrays keeps their layout: `slice`, `take`, `drop` and `reverse` that of the array they select from; `a ++ b` the narrowest that holds both (the same as theirs when they agree); `set` the array's, in place or in a copy, unless the new element doesn't fit it (possible only for an array used at a wider type), when the copy is one word per element. So every `Array U8` is packed, and an `Array U8` used as an `Array U32` (D71) stays packed. `set` is called through its wrapper function, which owns its arguments (D74), so it updates in place exactly when nothing else refers to the array. (g) **Generic code.** Where the element type is a type parameter, its layout comes from that type argument: type arguments already have an argument slot at run time, holding `0`; each now holds its type's layout word (a constant for a known type; a generic caller passes on its own parameter's). Nothing else about calls changes, and `0` still means one word per element. (h) **`format`** prints an array by how it is stored: a 1-byte unsigned array as `b"…"` (as `Bytes` print today), any other as its elements in brackets, `[1, 2, 3]`. So an `Array U8` used as an `Array U32` prints as `b"…"`; laying values out by type (D73) will remove that. | 11/13/2026 | (layout without monomorphising, every width, `Bytes = Array U8`) decided (11/13/2026); (a)–(h) **(proposed)** |
| D134 | **Arithmetic on a refinement gives its base number type (§3, D6, D38, D121).** Found 11/13/2026: `+ - * / %` gave their result the operands' type, so where that type was inferred (a lambda passed to `list.map`), `x + 1` for an `I8` `x` was an `I8` with nothing proven, and a function could prove `r == 0` though it returns 1 (`tests/types/arith_refined`). Now the result of `+ - * / %` is `Nat` if the operands' type is `Nat` or a refinement of it (`U8`, `Char`), else `Int` (`I8`, `Int`); `-` of `Nat`s keeps its obligation `a >= b` (D6, D121 c). A result is a narrower type (`I8`, `U8`) only where it is checked against that type, which proves it (E0450). Where the operands' type isn't known yet, the result's type is decided when it is (before the declaration's obligations are made). | 11/13/2026 | **(proposed)** |
| D135 | **Arithmetic keeps constant bounds (§3, D134, D133).** Decided (Ian, 11/13/2026): D134's result type keeps what is known of the operands' bounds, and an array's layout may come from them. Proposed, how: (a) Where each operand's bounds are constants (from a literal, which is its own bounds, or from its type: a fixed-width alias, `Char`, `Nat`'s `0`, or a range made by this rule), the result is that range, as an anonymous refinement: `x + 1` for a `U8` `x` is `(n~Nat, 1 <= n, n <= 256)`. Interval arithmetic: `+` and `-` add the bounds (crosswise for `-`; for `Nat` subtraction, whose obligation `a >= b` stands, the lower bound is at least `0`); `*` takes the least and greatest of the corner products; `/` (Euclidean, by a divisor known to be at least `1`) divides the outer bounds; `%` by a divisor bounded by `c` (in absolute value, never `0`) is `0 … c - 1`, and at most the dividend's upper bound if the dividend isn't negative. (b) A bound that isn't a constant (`n < len src`, a variable divisor) is dropped; with no bounds left the result is D134's `Nat` or `Int`. (c) The range is `Nat`'s refinement if its lower bound is at least `0`, else `Int`'s; a range equal to `Nat` is `Nat`. (d) A range's array layout (D133 e) is the narrowest that holds it: `U8`, `I8`, `U16`, `U32`, `I32`, `U64`, `I64`, else one word per element; so an array of `x % 16` is packed in bytes and prints as `b"…"` (D133 h). (e) The prover and messages see the range as written above; one value is `(n~Nat, n == 2)`. (f) Each operand's range comes from its own type (an operand needn't have the other's refinements, D71): `x + y` for a `U8` `x` and a `U32` `y` can pass 510. (g) A range isn't imposed on what it meets: the other operand of an operator is checked against its base type, so an unannotated `e` in `q + 1 < e` is a `Nat`; and the branches of an `if` or `match` whose type is inferred share their base type, the result being the hull of their ranges (`if b then x else 300` for a `U8` `x` is `(n~Nat, n <= 300)`), or the base if a branch has none. (h) Negation negates the operand's range. (i) Proving time is unchanged (the examples and `tools/checkers.ck`, measured against D134). | 11/13/2026 | (bounds kept; layout from them) decided (11/13/2026); (a)–(e) **(proposed)** |
| D136 | **Classes (M23–M25).** Decided (Ian, 11/13/2026): code generic over the types it uses goes through classes, as in Haskell ([Wadler and Blott 1989](https://homepages.inf.ed.ac.uk/wadler/topics/type-classes.html)), with classes as records ([Sozeau and Oury 2008](https://rocq-prover.org/papers/first-class-type-classes)), as Lean 4 has them, and their laws handed to the prover as Liquid Haskell's refined classes do ([Liu et al. 2020](https://www.cs.umd.edu/~mwh/papers/liu20typeclasses.html)). (a) A class lists what every instance must supply: functions (`fn`, a signature without a body) and lemmas (`lemma`, a statement without a proof). A class's laws are written `lemma`, the keyword proofs already use; there is no separate `law`. (b) Coherence is Rust's orphan rule ([RFC 2451](https://rust-lang.github.io/rfcs/2451-re-rebalancing-coherence.html)), with the package (D107) in place of the crate: an instance is declared in the package of its class or of its type's head constructor. (c) In scope, each in its milestone: classes over higher kinds (`Functor`, M25) and operators as class methods (M24). Proposed, how: (d) **Declaring.** `export class Ord a` with indented members; only requirements go in a class, and a lemma that follows from them is an ordinary generic lemma beside it (`export lemma refl x : Ord a, x~a`), proved once. (e) **Instances.** `instance Ord (List a) : Ord a` (the part after `:` is what the instance needs) gives each `fn` a body and may give each `lemma` a `proof`; without one Z3 proves it, as for any lemma. Each lemma is an obligation with the instance's functions in place of the class's. Built-in types' instances are proved too. (f) **Using.** A class applied to a type is a clause of a signature, beside the predicates: `fn sort xs -> r : Ord a, xs~List a, …`; D10 binds `a`. A class's functions are named `Ord.le`, or `le` where the class is imported unqualified. (g) **Coherence, further.** No two instances overlap; an instance's head is a type constructor applied to distinct type variables (Haskell 98), so finding an instance terminates and never backtracks; no instances for every type (`instance C a`) yet. A second order on a type is a wrapper type with its own instance, or `sort_as` / `sort_by` (D138). (h) **At run time.** Each class clause is one argument: a record of the class's functions; lemmas are erased (multiplicity 0, D124). An instance that needs nothing is a constant (no reference counting); one that does is built where it is needed. Code isn't specialised per instance (as D133 doesn't monomorphise); calling a known instance's function directly is an optimisation for later, measured. (i) **In the prover.** By coherence, a class function at a type is one function: at a type parameter it is uninterpreted, on that parameter's sort; at a known type it is the instance's body, reflected. A class lemma is used with `have Ord.trans x y z`, never given to Z3 as a quantified formula. (j) `==` stays D125's, not a class; class lemmas use it as equality. (k) Operators on known number types keep D134 and D135 (their meaning in Z3, their ranges, packed layouts); classes are for other types and for type parameters (M24). (l) `class`, `instance` and `forall` (D137) become keywords; `tools/lsp.ck` names a variable `class` and is renamed. | 11/13/2026 | decided (11/13/2026; (d)–(l) accepted with M22–M25) |
| D137 | **Named `forall` hypotheses (M23).** Decided (Ian, 11/13/2026): a signature may state a property of all values, under a name: `trans: forall x y z : x~a, y~a, z~a, le x y, le y z implies le x z`. (a) Where the function is called it is an obligation, which Z3 proves with fresh variables for `x y z` (the direction that needs no quantifiers); the caller writes nothing more. (b) In the function's body and proofs it is a hypothesis used only by name, `have trans p q s`, as a lemma is; it is never given to Z3 as a quantified formula, so proving stays within D101's predictable work. (c) Class lemmas (D136) and these hypotheses are one mechanism: an instance's lemma is a named `forall` proven once. (d) Using such a hypothesis without naming it (Z3 choosing values by triggers, as Dafny does) may come later, opt-in, without changing what is written. (e) Where it may appear: anywhere positive in a named precondition of a `fn` or `lemma` (the clause itself, under `and` or `or`, after `implies`, inside another `forall`), since there the call proves it with fresh variables: `h: n > 0 implies forall i : i~Nat, i < n, p xs[i]`. A `forall` in a negative place (before `implies`, under `not`) would be assumed at the call and become an `exists` in the body, so it is an error, with a `help:` suggesting a hypothesis of its own. (f) A precondition containing a `forall` must be named: the body can use it only by `have`, since it is not given to Z3 as the other preconditions are. (g) `have h a b c` fills in the `forall`s' variables, left to right, and gives what remains, without quantifiers, as a fact (`have h i` above gives `n > 0 implies (i < n implies p xs[i])`). (h) Not yet: `forall` in types and aliases (their predicates are assumed wherever a value of the type is, and D71 and D83 compare them by implication, so both directions would need quantifiers); it comes with instances passed explicitly. `forall` in postconditions comes when a use needs it, used by the caller by name (`have sort.sorted r i j`). Proposed: (i) a `forall`'s variables are bound only in it; its clauses are constraints like a signature's, the last its conclusion. | 11/13/2026 | decided (11/13/2026) |
| D138 | **Sorting in the standard library (M23).** Decided (Ian, 11/13/2026): `sort xs` (by `Ord a`), `sort_as key xs` (by `Ord k` on `key x`), and `sort_by le xs` (by a comparison function, with the named hypotheses `trans` and `total` of D137), each promising that the result is sorted and a permutation of `xs`. Proposed: (a) for `List` and `Array`, stable merge sorts written and proved in Checkers, not builtins; (b) `Bag a` and `perm` for any element type (D47 with `a → Int` in Z3, still without quantifiers); `sorted` by `Ord a`, `sorted_by le`; (c) `sort_as`'s order follows from `Ord k`'s lemmas at `key x`, so it needs function values in proofs (D139) and no hypotheses; (d) descending: `sort_as` with a reversed key, `sort_by (\x y -> x >= y)`, or a wrapper type. (e) `Ord`'s function is `le` (`<=` from M24); `String` is ordered by Unicode scalar values (the same as UTF-8 byte order); the instances for the prelude's types are in the prelude beside `Ord`. (f) This generalises D47: `Bag a` is a multiset of any element type. | 11/13/2026 | decided (11/13/2026) |
| D139 | **Function values in proofs (M22).** Decided (Ian, 11/13/2026): its own milestone, wanted with or without classes. Today Z3 sees through only named functions and lambdas with no free variables; any other function value makes an obligation fall outside the fragment (§7.3). Proposed, how: (a) a function type is an uninterpreted sort with `apply`, as Liquid Haskell and F\* encode them; (b) a named function, a partial application or a lambda (with its captured variables as arguments) gets its defining equation for `apply`; (c) so lemmas may take function parameters and be proved, e.g. about `list.map f` for any `f`. | 11/13/2026 | decided (11/13/2026) |
| D140 | **Order after M21 (§10).** Decided (Ian, 11/13/2026): M22 function values in proofs (D139); M23 classes, instances, class lemmas, named `forall` hypotheses and sorting (D136–D138); M24 operators as class methods and algebraic classes; M25 classes over higher kinds and `Functor`. | 11/13/2026 | decided (11/13/2026) |
| D24 | **Development loop:** Claude owns the implementation; Ian drives with examples. An issue is "found X, expected Y" with a `.ck` snippet. Each one becomes a regression test under `tests/` *before* the fix lands, and the spec is updated first whenever the expectation changes the language. | 11/05/2026 | decided |
| D25 | **Milestones reordered for CLI tools first** (§10): a running interpreter with `IO` comes right after type checking, before the prover, so Checkers can be used to build its own tooling early. ~~Capstone: an interactive shell with a small scripting language, with proofs of its correctness.~~ (removed by D81) | 11/05/2026 | decided |

---

## 1. Architecture

```
 .ck source
    │ parse
    ▼
 Surface AST ──elaborate──▶ Core terms (QTT)
    │  (constraints → Π/Σ/refinements,          │
    │   implicit args, pattern matching          │ prover obligations ──▶ Z3 (trusted, D1)
    │   → recursors, unification)                ▼
    │                                     Erasure (drop all 0-multiplicity content)
    │                                            ▼
    │                                     Runtime IR ──▶ Cranelift (M8, D80): in memory for `run`,
    │                                                    `check` and staging; executables for `build`
```

**What is trusted (D130).** There is no kernel that checks the elaborator's work again, so every part that decides whether a program is accepted is trusted: a bug in any of them can accept a wrong program.

- The **parser and elaborator**: names and types, refinements and their variance, pattern matching and exhaustiveness, usage (`own`/`ghost`, §2), termination (§5.3), and the obligations they hand the prover (`src/syntax`, `src/elab`, `src/usage.rs`, `src/core.rs`).
- The **translation to SMT-LIB** (`src/verify/smt.rs`) and **Z3** (D1), which proves the obligations.
- The **code generator and runtime** (`src/native`, `rt`, the Rust compiler): they run programs, and they also prove facts by evaluation (a `check`, an obligation or a lemma about closed values, listed as `computed` in the ledger).
- The standard library's **axioms** (D56) and its **builtins' signatures** (their conditions are facts about Rust code); `check`s and Rust tests compare them with the code on samples.

The trust ledger (§7.4, `checkers trust`) lists, for each file, what its proofs rest on. A kernel that checks core terms independently is later work.

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
          | Holds φ                       φ : Bool holds; erased (D124)
          | (x :π A) → B                  dependent function type
          | λ x. t                        abstraction
          | t u                           application
          | (x :π A) × B                  dependent pair type
          | (t, u)                        pair
          | let (x, y) :ρ = t in u        pair elimination
          | let x :ρ A = t in u           local definition
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

Σ, let, and equality follow the same pattern (Atkey 2018 §2 for Σ/⊗). Universes are cumulative and predicative: `Type ℓ : Type (ℓ+1)`. `Holds φ : Type 0` for `φ : Bool` (D124).

**Proof binders are erased automatically:** any binder of type `Holds φ` is forced to multiplicity 0. Users never write multiplicities on proofs.

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
- **Surface form:** `decreasing e` on the first line of a function body gives the measure. `e` is a `nat` or a tuple of `nat`s, compared lexicographically. Mutually recursive functions share one measure space; each call must strictly decrease it (worked example: `value`/`array`/`elements` in `stdlib/json.ck`).
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
| weakened refinement (D83) | a value whose refinement is replaced by a weaker one in a covariant position (`List (n~Int, n >= 6)` as `List (n~Int, n >= 5)`) | for any `n`: the found predicates imply the expected ones |
| call of a function-typed value (D84) | `f a` where `f`'s type has preconditions | the preconditions at `a`; afterwards its postconditions at `a` and `f a` are facts |
| function passed as a value (D85) | a named function, partial application or lambda passed where a function type is expected | for any argument: the expected precondition implies the function's own; with it, the function's postcondition implies the expected one |
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
2. **SMT:** translate Γ and ¬φ to SMT-LIB and ask the linked-in Z3 (§7.3, D46). On `unsat`, φ is proven, and the ledger records `smt φ` with the query's hash. Weaker queries come first, since `unsat` from a weaker query is still a proof (M12): (a) every reflected definition uninterpreted, fast when the facts in scope (`have`) already suffice; (b) only the definitions the goal mentions, so Z3 doesn't unfold functions whose results the facts give; (c) every definition, without the quantified postconditions of other functions; each with a smaller work limit (D101), since giving up on one only means trying the next. Then (d) the full query, whose counterexample is real; if Z3 gives up on it, a counterexample from (c) with the full limit is shown. Z3's answers are cached (D100).
3. **User proof:** a `lemma`'s `proof` block (D13, D49), or `have` facts added before the obligation arises.

On failure (D48), the error shows the obligation, the facts in scope, and Z3's counterexample when one exists.

### 7.3 SMT fragment (v0.1)
Decidable fragment, following Liquid Haskell: quantifier-free linear integer arithmetic, booleans, equality, datatypes, arrays and uninterpreted functions. Mapping:

| Checkers | SMT-LIB |
|----------|---------|
| `Int`, `Nat`, `U8`, … | `Int`, with `n >= 0` for `Nat` and the alias's predicates for refinements |
| `Bool` | `Bool` |
| `==`, `!=`, `<`, `<=`, `+`, `-`, `*`, `/`, `%` | native (`div`, `mod`: Euclidean, like Checkers) |
| `Array a` (and `Bytes`, `Array U8`) | `(Seq S)` for `a`'s sort `S`; `len`, `a[i]`, `++` native; each `a[i]` is known to satisfy the element type's refinement (`< 256` for `U8`) (D133) |
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

If Z3 rejects a query, which is a checkers bug, the obligation is reported unproven, never proven. A definition recursing by `decreasing` is given to Z3 only where its recursion ends (D118): `f x = if D then body else f#outside x`, where `D` is its `Nat` parameters being non-negative and, if its termination depends on them, its preconditions; elsewhere its value is unknown, so an equation such as `half 0 = 1 + half 0` (no solution) never reaches Z3. Calls in specifications must meet their callees' preconditions, as calls in bodies do, so a specification can't name a value no program computes.

Lemmas are not added automatically; `have` brings one in. **(proposed)** An `@auto` attribute on an exported lemma adds it to every query in importing modules (F\*'s SMT patterns), for very common facts only.

### 7.4 Trust ledger (D1)
Each module records every fact it relies on without a kernel-checked proof: obligations proven by Z3 (kind, location, Z3 version, query hash), `admit`s, and `check`s proven by evaluation. `checkers trust FILE.ck` prints the ledger of a file: its own entries, a summary of each standard-library module it loads (D110), and the builtins it relies on, whose Rust code is trusted. This is the only place Z3 enters the trust base, and the hook for future certificate checking.

`admit` (D13) is recorded as an unproven assumption. Development builds allow it; `checkers build --release` (M18, D116) refuses a program whose transitive ledger contains one, with error E0455 at each `admit` and exit status 1. Axioms (D56) are allowed. `--release` can't be combined with `--unverified` (a usage error, exit status 2), and for now it does nothing else.

### 7.5 Refined types inside types (M10, D82–D87)

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
  = help: pass a function that accepts every `Big`
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
| `term` | `Term` | stdin, stdout, stderr (each also as a `File`, D112), terminal modes |
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

**Streams (D112).** Every byte stream is a `File`: an open file, the standard streams (`terminal.stdin term`), and the pipes of a child process. The same operations read and write all of them:

```
let input = terminal.stdin term
header <- files.read_line input          # Content-Length: 52
body <- files.read_exactly 52 input      # (Result Bytes IoError, File)
files.close input

match proc.spawn "ckc" ["check", "--json", path] (Streams Discard Pipe Inherit) p
    Ok (Spawned child () out ()) ->           # out~File: only stdout is piped
        text <- files.read_rest out           # (Result Bytes IoError, File)
        files.close out
        let code = proc.wait child            # consumes the Child: Result Nat IoError
        …
    Err e                        -> …
```

The fields of `Spawned ss` have types computed from `ss`:

```
fn pipe_end s -> t : s~Stream, t~Type
    match s
        Pipe -> File
        _    -> Unit

record Spawned ss : ss~Streams
    child~Child
    stdin~pipe_end ss.stdin
    stdout~pipe_end ss.stdout
    stderr~pipe_end ss.stderr
```

So a program gets a `File` for each stream it piped and nothing to handle for the others, and the checker makes it close each one.

`proc.run "ckc" args input p` does the same in one call and returns `Output { code, stdout, stderr }`.

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

The worked example for this section is `std.json` (`stdlib/json.ck`; `examples/json.ck` uses it): an RFC 8259 parser and renderer whose bounds checks, termination, error positions, and object-key uniqueness are proven, plus a round-trip theorem. Decisions: D8–D23.

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
                                                                --   '(' [lname '~'] expr '->' [lname '~'] expr { ',' expr } ')' a refined function type (D82)
              | expr                                         -- predicate (a Bool expression)

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
| predicate in a constructor/field list | invariant (D11) | `Holds` field, erased |
| free `lname` in a type position, not in scope (`a` in `xs~List a`) | implicit type parameter (D10); a name used as a qualifier (`future` in `future.Future`) is never auto-bound | `{a :0 Type}` |

A constraint is only required where inference fails; `fn is_ws b : b~U8` infers its `Bool` result.

| Surface | Core (§3, §5) |
|---|---|
| `fn f x y -> r : x~A, p x, y~B, r~R, q x y r` | `def f : (x :ω A) → (_ :0 Holds (p x)) → (y :ω B) → {r : R \| q x y r}` |
| `enum Option a : a~Type` + `None` / `Some x : x~a` | inductive `Option (a : Type)` with two constructors |
| `Obj fields : fields~List (String, Json), unique (keys fields)` | constructor `Obj : (fields :ω …) → (_ :0 unique (keys fields)) → Json` |
| `record R p : p~T` + fields | single-constructor inductive + projections `r.field` |
| `type Hex16 = n~Nat, n < 0x10000` | `def Hex16 := {n : Nat \| n < 0x10000}` (transparent) |
| `lemma l xs : C` / `ensures φ` / `proof …` | `def l : (xs …) → (_ :0 Holds C) → Holds φ`, `φ : Bool`, all erased |
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
| `Type` | universes; declared in the prelude (D132) | D124 |
| `Bool`, `Unit` (`()`) | enum | |
| `Int` | builtin | arbitrary precision (D6) |
| `Nat` | refinement of `Int`: `n~Int, n >= 0` (D121) | arbitrary precision |
| `U8`, `U16`, `U32`, `U64`, `I8` … `I64` | refinement aliases of `Int`/`Nat` | D6 |
| `Char` | refinement of `Nat` | Unicode scalar value (no surrogates) |
| `(a, b, …)` | tuple | core Σ type; `.0`, `.1` or patterns |
| `Option a` | enum | `None`, `Some x` |
| `Result a e` | enum | `Ok x`, `Err x`; works with `try` |
| `List a` | enum | `[]`, `x :: xs`, `[1, 2]` |
| `Bytes` | `Array U8` (D133) | `b"…"`; packed, one byte per element |
| `String` | builtin | valid UTF-8 (D20); `string.bytes s` gives its `Bytes` |
| `Array a` | builtin (D133) | O(1) `len` and index; `std.array`; arrays of fixed-width numbers packed |
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
| M10 | Refined function types (D52, §7.5, D82–D87): refinements written inside types, predicates in function types, refinements compared by implication, preconditions checked and postconditions known at calls of function-typed values, partial applications everywhere (lifts D51, retires E0453) | `list.map (at_least 5) xs` checks when `xs~List (n~Int, n >= 5)`; every case in `tests/types/refined_fn_types.ck` gives the output marked there (done 11/06/2026) |
| M11 | The build tool and the formatter (D90–D93, D95–D98, §15.1–15.4): `ckc` (the renamed compiler); the M11 standard library additions; `checkers` written in Checkers, passing compiler commands to `ckc`; `checkers fmt [--check] [PATH]...` and `checkers fmt -`; the golden tests build `checkers` with `ckc` once and use it | `checkers fmt --check` passes on every `.ck` file in the repository (after one reformatting commit, if needed, whose diff Ian reviews); for each of them, formatting is a fixed point and `ckc parse` gives the same output before and after; every case in `tests/fmt/` gives its `.out`; `checkers check`, `run` and `build` behave as `ckc`'s (done 11/10/2026; `tests/parse/` and `tests/check/` keep their unformatted inputs, §15.4) |
| M12 | Faster checking (D100–D102): measurements (11/10/2026, release build, 2 cores): `ckc check examples/json.ck` takes 15 s, of which elaboration 27 ms, `check`s 61 ms, proving 15.2 s; two of its 364 queries (the `have` steps at lines 354 and 393 of the round-trip proof) take 4–10 s each, against a 10 s timeout, so the result depends on load (the vendored Z3 sometimes gives up); the other 362 take 1.3 s together. `tools/checkers.ck`: 0.28 s to check, 0.56 s to build. Work: the proof cache (D100); `rlimit` (D101); the two slow queries made fast, by giving Z3 less to search (only the facts the goal needs) or by splitting the proof steps | `ckc check examples/json.ck` under 2 s from scratch and under 0.3 s again with nothing changed or after a one-line change to a function the proofs don't use; every obligation in the repository proved with the same answer on every run and machine (vendored and pip Z3 alike) (done 11/10/2026: 1.2 s from scratch, 0.21 s again, 0.22 s after a one-line change to `parse`; the work limit is 6 000 000 for the full query and 1 000 000 for the weaker ones, from measurements over the repository; the same answers with the vendored and pip Z3) |
| M13 | The standard library restructured (D103–D106, §16.1–16.3), kept small: `std.` names and last-component qualifiers (D105); the standard library read from disk as the package `std` (D104), its proofs checked with programs; builtins one Rust file per module; `ckc trust` lists the builtins a program relies on; `std.json` from `examples/json.ck` (the manifest needs it) | every standard-library module is imported as `std.…` in `examples/`, `tools/`, `stdlib/` and the tests; every builtin is in the §16.3 table; `std.json` checks with its proofs (done 11/10/2026: `CHECKERS_STD`, `../lib/checkers/std` or the source tree's `stdlib/`; builtins in `rt/src/builtins/<module>.rs`; E0223 and E0361 for a broken standard library; `examples/json.ck` now reads JSON on standard input with `std.json`; checking `examples/json.ck` proves the 325 obligations of `std.json` and those of `std.list` too: 1.8 s from scratch, 0.21 s again (release build, 2 cores); output choices in D110) |
| M14 | Packages (D107–D109, D111, §16.4): `checkers.json`, `checkers.lock`, `--package`, `checkers build` / `check` / `run` for a package, `git` and path dependencies, minimal version selection | a package depending on a git package and a path package builds, its `trust` ledger lists both, and changing a dependency's version in `checkers.json` rebuilds with the new one (done 11/11/2026: `tests/packages.rs` builds a package with a path dependency that has a git dependency, from local repositories; checks its ledger, an upgrade through `checkers.json`, a moved tag, two major versions, an undeclared import and manifest errors; choices in D111) |
| M15 | Streams and processes (D112, §8.4): `File` for every file (open files, pipes, the standard streams); `read_some`, `read_exactly`, `read_rest`, `write_bytes`; `terminal.stdin`/`stdout`/`stderr`; `proc.run`, `proc.spawn` with `Spawned ss`, `proc.wait`; first, the resource check fixed for types that depend on values not known where they are used, and E0401 showing the computed type | every example, tool and test that reads or writes a stream uses the new operations where they fit; golden tests for the resource-check fix and each new operation; `tests/run/` cases for `proc.run` and `proc.spawn` (done 11/11/2026: the resource check now computes field types from known arguments and treats a type that depends on an unknown value as a resource (`tests/types/resource_computed`); a resource used up inside an argument is used once, since arguments are evaluated before the call, while what can be part of the argument's value is still scaled (`tests/types/resources_nested`); E0401 points at the name in a pattern; a variable hiding a module gets a `help:`; `examples/copy.ck` copies bytes exactly in 64 KiB blocks and `examples/wc.ck` streams its input (9.7 MB in 0.54 s, matching the system `wc`); the build tool reads git's output with `proc.run`, so git's own messages no longer reach the terminal; `tests/run/streams`, `streams_misuse`, `processes`) |
| M16 | Blocking operations free the thread (D113, §13.8): a stack per behaviour, a poller, a thread pool for calls that can't be polled | the done-when list of §13.8 (done 11/11/2026, Linux x86-64: `tests/run/waits.ck`, four readers waiting on `cat` children for a writer scheduled after them, finishes on 1, 2, 3 and 8 threads (`tests/parking.rs`); a behaviour reading standard input lets another print on one thread; `tests/stress/` passes; `bench/behaviours.ck` on one thread 63.7 ms minimum, 74.6 ms median over 25 runs, against 59.3 and 67.9 before (+7%, +10%), on two threads within noise; a behaviour recurses a million deep; choices in D117, proposed) |
| M17 | Reflected definitions sound for every recursion (§7.3's known gap): a definition recursing by `decreasing` is given to Z3 only where its recursion ends, with typing predicates and fuel as Dafny and F\* do | (D116) first, a test in which today's encoding lets Z3 prove something false from such a definition, which then fails with the expected message; every example, tool and `std` module still proves; proving time measured before and after; if no such test can be found, the encoding stays and §7.3 records what was tried (done 11/11/2026: no false proof found; the gap shown with a quantified axiom, and a hang found and removed; guarded definitions and checked specifications, D118, proposed; `tests/types/reflect_domain`, `spec_preconditions`; proving time 8.7 s → 7.6 s) |
| M18 | No `admit`s in what ships, and release builds that refuse them (§7.4): `std.json`'s two `admit`s (`string_render`, `members_render`) proven; `ckc build --release` (and `checkers build --release`) rejects a program whose transitive ledger has an `admit`, naming each (axioms stay allowed, D56); for now that is all `--release` does (D116) | `ckc trust examples/json.ck` lists no `admit`; a golden test of `--release` rejecting a program with an `admit`; every example builds with `--release` (done 11/11/2026: both lemmas proven, from six axioms about characters and strings and `chars`, D119, proposed; `tests/tool/commands` builds `tests/tool/admitted.ck` with `--release` and gets E0455; every example with a `main` builds with `--release`; proving the examples, tools and standard library without the cache 7.1 s → 13.1 s, because the three programs that load `std.json` each re-prove its new lemmas, D109) |
| M19 | `checkers lsp` (D120, §15.5): diagnostics on every change (types first, then proofs), hover, go to definition, semantic highlighting, formatting, document symbols | the scripted sessions in `tests/lsp/` (requests in, expected responses out) pass; type errors reach the client in under 100 ms on `tools/checkers.ck` (measured); Ian confirms it works in Emacs with Eglot |
| M20 | Checking past errors and `Nat` as a refinement of `Int` (D121, D122), `main` on a fiber (D123) | `Int` and `Nat` mix and convert as D121 says, with golden tests; proving time measured before and after; a file with a syntax error and a type error still gets the other declarations' type errors, proofs and `check`s (golden tests in `tests/types/`, `tests/json/`, `tests/lsp/`); a program reading standard input in a loop in `main` runs its behaviours on one thread (`tests/run/`) (done 11/11/2026: `tests/types/nat_int`; checking every example, the tool and `std` with no cache about 31 s before and after, the tool's 347 obligations unchanged; `tests/types/past_errors`, `tests/json/past_errors`, `tests/lsp/past_errors`; `tests/run/main_waits`) |
| M21 | Arrays (D133, §9.5): `Array a` in the prelude, `Bytes` as `Array U8`, `std.array`, packed layouts for every fixed width, layout arguments for generic code, the prover's `(Seq S)` | every existing test, example and tool gives the same output with `Bytes = Array U8`; `tests/run/` cases for each packed width (signed, unsigned, `U64` beyond 63 bits), for generic code creating arrays of `U8` (packed, printed as `b"…"`), for `set` in place and copied, and for an `Array U8` used as an `Array U32`; `tests/types/` for indexing and `==` on arrays; proofs about `std.array`'s postconditions; `examples/wc.ck` as fast as before | done (11/13/2026): `tests/run/arrays` (every width at its edges, `U64` and `I64` past 63 bits, `Bool`, `Char`, generic `map` to `U8` packed and printed as bytes, `set` on a shared array copying and on an unshared one in place, an `Array U8` used as an `Array U32` widened by `set`), `tests/types/arrays` (an `Int` element isn't a `U8`, with the counterexample `array.from_list [256]`; `==` on an array of functions, E0263; out of bounds), `std.array`'s own `check`s, layout unit tests in `rt/src/array.rs`. Indexing an `Array U8` stays inline without checking the object's kind (it is always bytes); `len` of a string, bytes or array is now inline too, so `examples/wc.ck` is about 3% faster than before |
| M22 | Function values in proofs (D139): function types as uninterpreted sorts with `apply`, defining equations for named functions, partial applications and lambdas | `std.string.concat_map_chars` proved instead of `__builtin`; a lemma about `list.map f` for any `f` proved; a call of an unknown function value's postcondition used in a proof (D84); `tests/types/` cases for each; proving time measured before and after |
| M23 | Classes and sorting (D136–D138): `class`, `instance`, class clauses in signatures, class lemmas as obligations, coherence (orphan rule, no overlap), records of functions at run time; named `forall` hypotheses; `Ord` in the prelude; generic `Bag a` and `perm`; `sort`, `sort_as`, `sort_by` for `List` and `Array` | `list.sort` and `array.sort` proved sorted and permutations for any `Ord a`, and used at `Int` and `String`; `sort_by (\x y -> x >= y)` checks with nothing more written; an instance missing a lemma, a false instance lemma, an orphan and an overlapping instance each give a precise error (`tests/types/`); `examples/sort.ck` uses the generic sort |
| M24 | Operators as class methods (D136 c, k): `+ - *`, negation and comparisons for types other than known numbers; algebraic classes with lemmas (`Semigroup`, `Monoid`) | a user type with `+` and `<=` through instances, its lemmas used in a proof; every existing test gives the same output (numbers unchanged); proving time unchanged |
| M25 | Classes over higher kinds (D136 c): parameters like `f~(Type -> Type)`, first-order unification of `f a`, variance; `Functor` with its identity and composition lemmas | `Functor` instances for `List`, `Option` and `Array`, their lemmas proved; a function generic over any `Functor` checks and runs |

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
  - The prover tests need Z3 (D46).
- A report from Ian is "found X, expected Y" with a `.ck` snippet. It is added as a failing golden test first, then fixed. If Y changes the language, this spec is updated before the code.
- **Past errors (D122).** Every declaration the parser recovers is type-checked; a function whose body fails to parse keeps its header, so its uses see its signature. A declaration has errors if one of its diagnostics is an error. Set aside, and not reported: the obligations inside a declaration with errors, the obligations and `check`s that mention one (or a definition or type using one, transitively), and the `check`s written with errors. Everything else is proven and run. A program with errors is still never run or built.
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
- `==` compares values structurally. Comparing functions, capabilities, cowns, futures, files or process handles, or values containing them, is a type error (D125).
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

### 13.8 Blocking operations (M16, D113)

Today a behaviour that waits for input, for a child or for a pipe to drain holds its thread: with `--threads N`, N waiting behaviours stop the program. From M16 a wait parks the behaviour instead, and the thread runs others, as goroutines in Go and fibers in Eio do. Programs don't change.

- **Platforms (D116, D126).** Linux on x86-64 and macOS on ARM64.
- **Stacks.** Each behaviour runs on a stack of its own, so it can be suspended in the middle of a call. Stacks come from a pool and are reserved, not committed: address space for the deep recursion D75 allows (256 MiB), memory only for the pages a behaviour touches, a guard page below. Switching stacks saves and restores the callee-saved registers, a few nanoseconds; M16 measures it against the 1.5 µs a behaviour already costs (§13.7).
- **Waiting.** Pipes, terminals and (later) sockets are non-blocking; a read or write that would block registers the descriptor with a poller (`epoll` on Linux, `kqueue` on macOS, D126) and parks the behaviour, and a poller wakes it when the descriptor is ready. Reading a regular file and `waitpid` can't be polled; they run on a separate pool of threads while the behaviour is parked (Go's hand-off; `io_uring` may replace this on Linux later). `clock.sleep` is a timer in the poller.
- **What stays the same.** A parked behaviour keeps its cowns: behaviours waiting for those cowns still wait, in the order they were scheduled, so causal order and freedom from deadlock hold (§8.5). Terminal calls stay atomic (D68). With `--threads 1` the order in which parked behaviours resume follows the order their input arrives, so golden run tests stay deterministic when only one behaviour reads at a time.
- **Done when** (M16): with `--threads 2`, a program whose behaviours wait on more pipes than it has threads finishes; the language server's reader keeps no thread while it waits; `tests/stress/` passes; the cost of a behaviour that doesn't block stays within 10% of today's.
- **As built** (D117): `rt/src/fiber.rs` (stacks, the switch, `park`, `blocking`, a lock that parks), `rt/src/poll.rs` (`epoll`, non-blocking pipe ends), `rt/src/blocking.rs` (the blocking pool). A finished fiber waits for its next body, and each worker keeps up to 64, so a behaviour that doesn't wait costs one round trip onto a reused stack, 41 ns.

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

**Arrays (D133).** An array object's header gives its length and how its elements are stored: one word each, or packed at 1, 2, 4 or 8 bytes, signed or not. Reading goes by the header. Code that creates an array from elements lays it out for its element type: every type argument is passed as its layout's word, in the argument slot it already had (until now `0`), so a generic function knows the layout of each of its type parameters and passes it on. `++`, `set` and slicing keep their arrays' layouts (D133 f).

**Memory (D74).** Functions receive their arguments owned and consume them. Each variable a function binds goes to the last part of an expression that uses it; earlier parts borrow it, and a borrowed variable is duplicated only where it is kept (returned, stored, passed on). Primitives and builtins borrow their arguments. A `match` duplicates the fields its arm uses; if the arm doesn't use the value matched on, it is dropped, and if the arm builds a constructor with as many fields, the drop becomes a *reuse*: when it was the only reference, the new value is built in its memory. Counts are atomic. Constants (definitions without parameters) are computed on first use and kept for good. `CHECKERS_RC_CHECK=1` counts the objects left at exit (only constants' values should remain); `CHECKERS_NATIVE_DUMP=1` prints the first-order code with its reference counting.

**Calls (D75).** Every function uses Cranelift's `tail` convention; calls in tail position are `return_call` or `return_call_indirect`, so tail recursion runs in constant stack. Code runs on stacks of 256 MiB: every behaviour's fiber, `main`'s too (D123), reserved but only touched as used. The runtime calls compiled code through a generated trampoline, `ck_invoke`.

**Runtime.** `checkers_rt`: allocation and freeing, big integers (`rt/src/num.rs`), the `__builtin`s of `stdlib/` (`rt/src/builtins/`), `format` and `==`, I/O with atomic terminal calls (D68), behaviours and `par`, the scheduler, fibers, the poller and the blocking pool (§13.8), and runtime errors (``runtime error in `f`: …``, exit code 70). Native code describes its constructors and definitions to the runtime in a short text descriptor. `checkers build` links with `libcheckers_rt.a`: the one named by `CHECKERS_RT_LIB`, else the newest next to the `checkers` executable or in `deps/` beside it.

**Scheduler (D77).** `rt/src/sched.rs`: Verona's per-resource queues with atomic links (§13.5), runnable behaviours on a lock-free queue (Vyukov's bounded multi-producer, multi-consumer queue, with a locked overflow), a worker running next the behaviour its own completion made runnable, and idle workers polling briefly before they sleep. A behaviour keeps the cells it names until it has released them.

**Compile-time evaluation (D80).** `src/native/eval.rs` keeps one in-memory module per checked program: each `check`, and each value staging computes, is compiled as a function of no arguments and added to it, with the definitions it needs (each compiled once), then run on a thread of its own. A runtime error there doesn't exit: the runtime reports it to the waiting compiler, which turns it into a diagnostic (E0261 for a `check`, E0273 in staging), and the stopped thread is left parked. The result is read back from its words: for staging into a term (numbers, strings, bytes, constructors, tuples; a function has no term, so its call stays at run time), for a failed `check` into the text `format` would give.

**Tests.** The golden runner runs each `tests/run/` case with the `checkers` binary; each stress case 10 times on 8 threads; and it builds two programs with `checkers build` and runs the executables.

**Dependencies.** `cranelift-codegen`, `cranelift-frontend`, `cranelift-module`, `cranelift-jit`, `cranelift-object`, `cranelift-native` 0.137 (all from the Bytecode Alliance, pure Rust; D5) and `target-lexicon`.

## 15. Developer tools (M11, M19; D90–D98)

Tools that help write Checkers are themselves written in Checkers: they are useful, and they show what the language can do at a larger scale than `examples/`.

### 15.1 The compiler and the build tool (D95, D96)

As with `rustc` and `cargo`, there are two programs:

| | `ckc`, the compiler | `checkers`, the build tool |
|---|---|---|
| written in | Rust | Checkers |
| built by | Cargo | `ckc build tools/checkers.ck` |
| does | `check`, `run`, `build`, `parse`, `stage`, `trust` on files; `--package`, `--uses` (D111) | the command people use: passes those commands to `ckc`; packages and their dependencies (M14, §16.4); `fmt`; later `lsp` (M19) |

```
tools/
  checkers.ck      `main`: the commands
  ck/syntax.ck     lexer and layout, keeping comments and blank lines: lines, logical lines and blocks
  ck/format.ck     the formatter, a pure function: fn format src -> r : src~Bytes, r~Result Bytes SyntaxError
  ck/manifest.ck   reading checkers.json and checkers.lock, with line and column for problems (M14)
  ck/packages.ck   dependencies: path and git, minimal version selection, the lock file, `ckc`'s flags (M14)
  fmt.ck           `checkers fmt`: files, --check, standard input
  lsp/protocol.ck  JSON-RPC framing and LSP messages over `std.json` (M19)
  lsp.ck           `checkers lsp` (M19)
```

The build tool is an ordinary program, compiled ahead of time, so starting it costs no elaboration or code generation (compiling a program the size of `examples/json.ck` takes about 0.13 s without proving, 14 s with it). It is proven like `examples/`: `ckc check tools/checkers.ck` must report zero diagnostics, which the golden tests check. During development, `ckc run tools/checkers.ck fmt …` runs it without building.

### 15.2 How the build tool drives the compiler (D97)

The build tool starts `ckc` as a process with its own standard streams (`proc.exec`): `checkers check FILE` is `ckc check FILE`, and its exit code is `ckc`'s. In a package's directory it first resolves the dependencies and adds `--package` and `--uses` (D111). The formatter does not involve the compiler at all: it reads bytes and writes bytes, one file at a time.

### 15.3 Standard library additions (D90)

The language already has what the tools need: total code with proven bounds and termination for the parser (as `json.ck` shows), `partial fn` for the server loop, and cowns for running the compiler beside the request loop. The standard library does not, today:

| Missing | Why | Addition |
|---|---|---|
| output without a newline | `checkers fmt -` writes the formatted file as it is | `terminal.write` (M11) |
| reading exactly *n* bytes | LSP messages are `Content-Length: n\r\n\r\n` + *n* bytes, on a pipe that stays open | `files.read_exactly` on `terminal.stdin` (D112, M15) |
| directory listing | `checkers fmt` with a directory | `files.list` (M11) |
| linear-time joining | `list.join` is `p ++ sep ++ join sep rest`, quadratic in the output | `string.concat` (M11); `list.join` keeps its definition, which proofs about rendering use (`std.json`) |
| byte slices, UTF-8 checking | lexing | `bytes.slice`, `string.from_utf8` (M11) |
| number parsing | `Content-Length` | `nat.parse` (M13) |
| JSON | LSP messages | `std.json`, from `examples/json.ck`, with its proofs (M13, done) |
| running a program | the build tool drives `ckc` (D97); the language server reads its diagnostics | `proc.exec` (share standard streams, M11); `proc.run` (capture output) and `proc.spawn` / `proc.wait` (D112, M15) |
| environment variables, the executable's path | finding `ckc` (D96) | `env.get`, `env.executable` (M11) |

`Map`, `Set` and `Array` (§9.5) are not needed for the first versions: the open documents are a short association list.

### 15.4 The formatter (D91–D93)

`checkers fmt` formats each `.ck` file under each `PATH` (default `.`) in place. `--check` changes nothing, lists the files that would change, and exits with `Failure 1` if there are any. `checkers fmt -` formats standard input to standard output, for editors.

The formatter keeps the line breaks the author chose and normalizes everything else, as gofmt does. The rules (D92):

- **Indentation:** 4 spaces per block level. A continuation line lines up with the first item after the open bracket it is inside, or after the `:` of a signature; otherwise it keeps the indentation its author gave it relative to the line it continues, at least 4 (D99).
- **Spaces:** one on each side of a binary operator, `->`, `<-` and `=`, and after `,` and a signature's `:`. None around `~`, inside `( )` and `[ ]`, after a unary `-` or `\\`, or around a glued `.` or `[` (D22); one inside `{ }` (D99). Application is separated by single spaces.
- **Alignment:** the `->` of the arms of one `match` line up (an arm with a guard is left out, D99), as do the `:` of the constructors of one `enum` (a constructor without constraints is skipped), unless a blank line separates them. Trailing `#` comments on consecutive lines start in one column; a blank line or a line without a trailing comment ends the run. The column is the furthest of each line's code end plus the spaces its author put before the comment, at least two (D99): a run that is already aligned stays aligned, wherever its code moves, and formatting twice changes nothing.
- **Blank lines:** at most one in a row; none at the start or end of a block; the file ends with exactly one newline. Trailing whitespace is removed.
- **Kept as written:** comment text, literals, the order of declarations and imports.

`tests/fmt/` has examples: each `.ck` is formatter input and its `.out` the output of `checkers fmt -` on it. The golden tests also require every `.ck` file in `tools/`, `examples/`, `stdlib/` and `tests/{types,run,stage,stress}` to be formatted, and every `.ck` file in the repository to format to a fixed point with the same syntax tree (`tests/parse/` and `tests/check/` keep their unformatted inputs, which test the lexer and parser).

### 15.5 The language server (M19, D120)

`checkers lsp` speaks LSP 3.17 over standard input and output. It is part of the build tool (D95) and runs the compiler as a process (D97), so the editor's diagnostics are the compiler's.

| Request or notification | Behaviour |
|---|---|
| `initialize` | advertises full document sync, hover, go to definition, find references, formatting, document symbols and semantic tokens (full document); UTF-8 positions if the client offers them, else UTF-16 |
| `didOpen`, `didChange`, `didClose` | stores (or drops) the text; kills the document's check in progress, if any (not other documents', D127 e), and starts one of the document with every open document as an overlay |
| `didSave` | nothing: proofs already run on every change |
| `textDocument/publishDiagnostics` | sent after each phase of a check: types, then `check`s, then proofs; each time with all diagnostics so far, for every file the check reached |
| `textDocument/hover` | the type of the name under the cursor, or a function's signature with its conditions, and its description (D128), from the index |
| `textDocument/definition` | the definition of the name under the cursor, from the index |
| `textDocument/references` | the uses of the name under the cursor in the open files' indexes, and its definition if `includeDeclaration` (D127 f) |
| `textDocument/semanticTokens/full` | names classified by the index (function, lemma, constant, type, constructor, field, parameter, variable, module) and keywords, comments, strings and numbers |
| `textDocument/formatting` | `format` from `tools/ck/format.ck`; a syntax error gives no edits |
| `textDocument/documentSymbol` | the file's declarations, from the index |
| `shutdown`, `exit` | ends the server, killing any check |

**From the compiler** (`ckc check --json`):

- One JSON object per line. Positions are `[line, column]` from 0, the column in bytes; paths are as the compiler opened them.
- `{"kind":"diagnostic","phase":P,"path":…,"start":…,"end":…,"severity":"error"|"warning","code":…,"message":…,"label":…,"notes":[…],"help":…}`, where `P` is `"types"`, `"checks"` or `"proofs"`; `label` and `help` may be `null`.
- `{"kind":"name","path":…,"start":…,"end":…,"class":…,"def":{"path":…,"start":…,"end":…} or null,"hover":…,"doc":… or null}`, where `doc` is the description of what the name refers to (the comment lines directly above its declaration, D128), for each name in the file being checked (the editor's document; its imports' names are found through their declarations, `def`).
- `{"kind":"token","path":…,"start":…,"end":…,"class":"keyword"|"comment"|"string"|"number"}`.
- The `name` and `token` lines come right after the types phase's `done` line (so its diagnostics don't wait for them), and are ended by `{"kind":"done","phase":"index"}` (D127 d), before the `check`s' diagnostics.
- `{"kind":"done","phase":P}` after each phase, always all four (`types`, `index`, `checks`, `proofs`). Errors don't stop the later phases (D122): they set aside only the `check`s and obligations that touch a declaration with errors.
- `--overlay FILE`: `FILE` holds a JSON object from paths to text; a path in it is read from there instead of from disk. `--overlay -` reads the object from standard input (how the server passes it).

The server keeps one cown for its output, so a reply and diagnostics published by a check never interleave, and one for what the checks share (the latest check, the diagnostics showing, the index); a check reads the compiler's output in a behaviour of its own, one phase per behaviour. Its loop runs in `main`, itself a behaviour (D123). Requests about a document are answered from the index of that document's latest check, waiting for it if it hasn't come yet (D127 c). Until a check's proofs are known, the previous check's proof diagnostics stay (so they don't flicker while typing); a check that ends without finishing a phase, unless a newer one killed it, is reported with `window/showMessage`, as is a compiler that can't be started. Tests in `tests/lsp/` are scripted sessions: a file of messages to the server and the messages expected back.

### 15.6 Documentation and the site (D131)

**From the compiler** (`ckc doc FILE`), one JSON object per line, from the syntax tree:

- `{"kind":"module","name":…,"doc":…}`: the module's name and description, the comment that opens the file (a first line `NAME.ck — Text` gives `Text`).
- `{"kind":"import","module":…,"as":…,"names":[…]}` for each import: the module, the name it is used by (`as`'s, else its last part), and the names it brings in unqualified.
- `{"kind":"decl","what":…,"name":…,"line":…,"signature":…,"doc":…,"items":[…]}` for each exported declaration, in source order. `what` is `fn`, `lemma`, `type`, `enum`, `record` or `let`; `signature` is the declaration as written up to its body (a lemma's up to `proof`; a long constant's value is left out); `doc` is its description (D128), or `null`; `items` are an enum's constructors or a record's fields (`{"name":…,"signature":…,"doc":…}`), none for an abstract type.

**`checkers doc DIR -o OUT [--name NAME] [--root PATH] [--label TEXT]`** documents the package in `DIR`: every `.ck` file under it, named by its `module` line. `NAME` defaults to the directory's name; `PATH` is the way from its pages to the site's root, for the site's links (default `../..`); `TEXT` names the version, shown on each page. It writes, as `.md` and `.html`:

| Page | Navigation, on the left | Content |
|---|---|---|
| `OUT/NAME/index` | its modules | `DIR/README.md` if there is one (without its first heading), then the modules, each with the first sentence of its description |
| `OUT/NAME/MODULE` | `NAME.MODULE`, whose `NAME` leads back to the package's page; then each declaration | the module's description (the comment that opens the file), then each exported declaration: its signature as a code block, its description. A record's or an enum's code block lists its fields or constructors, each with its description as a comment above it. |

`MODULE` is the module's name without the package's (`std.list` is `OUT/std/list`). The Markdown twins have the same content, without the navigation.

**Links in signatures.** Each type or constructor named in a signature links to its declaration, if the package declares and exports it. Names resolve as in the compiler: a qualified name (`files.File`) through the import it names; otherwise the module's own declarations, then the names its imports bring in, then the prelude. After `~` and until the next top-level `,`, a name is a type; elsewhere a constructor if there is one, else a type (D26). Type variables aren't links.

**`checkers site SRC -o OUT`** renders each Markdown page `SRC/PAGE.md` to `OUT/PAGE.md` and `OUT/PAGE.html`, and writes `OUT/llms.txt`: the site's title and summary (from `SRC/index.md`), then a link to each page and to every Markdown page under `OUT/docs/latest/`.

**HTML.** Pages are written in Markdown and rendered by `tools/ck/markdown.ck`, which handles headings, paragraphs, bullet and numbered lists, block quotes, fenced code, tables, links, emphasis and inline code; anything else is shown as text. Code blocks marked `checkers` are highlighted (keywords, comments, strings, numbers). Each page's head names its Markdown twin, `<link rel="alternate" type="text/markdown" href="PAGE.md">`, and the site's `llms.txt`, `<link rel="describedby" href="…/llms.txt">` (as [llmstxt.org](https://llmstxt.org/) proposes); the page shows no link to either. The top bar links the site's home, the tour, the documentation (always `/docs/latest/std/`) and the source; on a documentation page it ends with the version shown (`--label`) as a menu of the others, read from `/docs/versions.json` (`{"latest": "vX.Y.Z" or null, "versions": ["dev", "vX.Y.Z", …]}`, written by the Pages workflow). Choosing a version opens the same page in it, or that version's package page if the page doesn't exist there. Links within documentation stay within its version.

**Hosting.** GitHub Pages, from `.github/workflows/pages.yml`. It builds nothing: the site and `dev` come from the latest commit that passed CI on `main` (when CI passes, that run's commit), built with the `ckc` and `checkers` that CI run uploaded; each release's documentation comes from its archive. Publishing a release (or running it by hand) redeploys the same way, which adds the new release's documentation and leaves `dev` as it was. The documentation has one directory per version:

| Path | What |
|---|---|
| `/docs/dev/std/` | `main`, labelled `dev` |
| `/docs/vX.Y.Z/std/` | each release, as published |
| `/docs/latest/std/` | a copy of the highest release that isn't a pre-release (`v1.2.0-rc.1` is one); of `dev` while there is none |

`docs.md` links all of them, and `versions.json` lists them for the version menu; `llms.txt` lists `latest` only. A release's directory comes from the archive `checkers-vX.Y.Z-docs.tar.gz`, which the release workflow builds with the tag's own tools (`--root ../../.. --label vX.Y.Z`; it refuses a tag whose commit hasn't passed CI on `main`) and attaches to the (immutable) release, so a release's documentation never changes once published. The release workflow then starts the Pages workflow itself, since a release published by a workflow starts no other workflow.

## 16. Standard library and packages (M13–M14, D103–D109)

### 16.1 Layers (D103, D104)

| Layer | What | Where | Trusted |
|---|---|---|---|
| prelude | the types and operators the compiler knows by name | `stdlib/prelude.ck` and the compiler (`Prim`) | the compiler |
| builtin modules | functions implemented by the runtime: their contracts in `.ck`, their code in Rust | `stdlib/<module>.ck`, `rt/src/builtins/<module>.rs` (each file's `TABLE` names its builtins) | each builtin a program reaches: `builtin` in the ledger |
| Checkers modules | everything else | `stdlib/<module>.ck` | nothing: proven |

A module may mix builtin and Checkers functions (`std.string`: `concat` is builtin, a `join` over it would be Checkers). The standard library is the package `std`, shipped as source beside `ckc` and versioned with it (D104): editing it needs no rebuild, except for a builtin's Rust code. Go has done the same since 1.20: "packages in the standard library are built as needed and cached in the build cache, just like packages outside `GOROOT`" ([Go 1.20 release notes](https://go.dev/doc/go1.20)).

The models: Rust layers `core` (no allocation), `alloc` and `std` (the OS) ([Rust std architecture](https://mintlify.com/rust-lang/rust/architecture/standard-library)); in Checkers the capability discipline (§8) already separates code that needs the OS, by its types, so one library with capability modules does the same job. Go ships its standard library with the toolchain; Gleam ships `gleam_stdlib` as an ordinary package ([hex.pm](https://hex.pm/packages/gleam_stdlib/versions)), which works because its runtime is someone else's (Erlang, JavaScript).

### 16.2 Names (D105)

```
import std.list                     # list.map
import std.files (Fs, IoError)      # files.read; Fs and IoError unqualified
import json_schema.validate         # a dependency's module: validate.check
import parser.lexer                 # this package's parser/lexer.ck: lexer.next
import std.string as str            # str.concat
```

The first component of an import decides where it comes from: `std`; a dependency declared in `checkers.json`; else this package's files. Go reserves the same way, by giving standard-library paths no dot in their first element ([Go modules reference](https://go.dev/ref/mod)).

### 16.3 Contents (D106)

The standard library is these modules. Its scope is still to be settled (D106); until then it stays small: *planned* entries wait for that decision. Contracts are in each module's file. Every builtin the runtime implements is named in its module's row (a test checks this).

| Module | Layer | Exports | Status |
|---|---|---|---|
| `std.prelude` | prelude | `Type`, `Nat`, `Int`, `String`, `Array`, `Bytes`, `Bool`, `Unit`, `Option`, `Result`, `List`, `U8`…`U64`, `I8`…`I64`, `Char`, `not` | exists |
| `std.list` | Checkers | `length`, `map`, `all`, `reverse`, `join`, `keys`, `contains`, `unique`, `count`, `max_of`, `take`, `drop`, `sorted`, `perm`, lemmas (among them `keys_append`, `contains_append`, `contains_reverse`, `unique_split`, D119) | exists; planned: `filter`, `fold`, `find`, `any`, `zip`, `concat`, `index_of` with lemmas |
| `std.option`, `std.result` | Checkers | `map`, `and_then`, `or_else`, `with_default`, `is_some` / `is_ok` | planned |
| `std.bag` | builtin | `Bag`, `of`, `count`, `sum` (multisets, for permutation proofs, D47) | exists |
| `std.sort` | Checkers | `sort` with `sort_sorted`, `sort_perm` | planned (from `examples/sort.ck`) |
| `std.map`, `std.set` | Checkers | `Map k +v`, `Set k`: `empty`, `insert`, `remove`, `lookup`, `member`, `size`, `to_list` and their lemmas (`lookup_insert`, …), ordered keys (D15) | planned (§9.5) |
| `std.array` | builtin + Checkers | `from_list`, `to_list`, `repeat`, `init`, `map`, `set`, `slice`, `concat`, `reverse`, `all`, `contains`, `count`, `take`, `drop` (D133) | exists (M21) |
| `std.bytes` | builtin | `matches_at`, `slice`, `concat` | exists |
| `std.string` | builtin + Checkers | `bytes`, `from_utf8`, `from_char`, `from_chars`, `chars`, `concat`, `concat_map`, axioms relating them (D119) | exists; planned: `join`, `split`, `starts_with`, `ends_with`, `trim` |
| `std.char` | Checkers | `code`, `from_scalar`, `from_ascii`, `from_surrogates` (D119) | exists |
| `std.utf8` | builtin + Checkers | `decode_at`, `encode`, `encode_append`, `decode_from_char` | exists |
| `std.decimal` | builtin + Checkers | `Decimal`, `scan_json`, `render`, `of_int`, `continues_number` | exists; planned: `nat.parse` as `std.number` (`parse_nat`, `parse_int`, `render_nat`) |
| `std.cursor` | Checkers | `Parsed` (a parse result that consumed input) | exists |
| `std.json` | Checkers | `Json`, `Error`, `ErrorKind`, `parse`, `render`, `depth`, `MAX_DEPTH`, the round-trip lemma | exists (M13; proven without `admit`s, M18) |
| `std.path` | Checkers | `join`, `parent`, `name`, `extension` (paths as `String`, `/`-separated) | planned (the tools compute these by hand today) |
| `std.system` | — | `System`, `ExitCode`, the authority types | exists |
| `std.terminal` | builtin | `Term`, `print_line`, `eprint_line`, `write`, `write_bytes`, `read_line`, `read_all`, `stdin`, `stdout`, `stderr` | exists |
| `std.files` | builtin | `Fs`, `File`, `IoError`, `Entry`, `read`, `write`, `list`, `create_dirs`, `open`, `create`, `close`, `read_line`, `write_line`, `read_some`, `read_exactly`, `read_rest`, `write_bytes`, `flush`, `within`, `describe` | exists |
| `std.env`, `std.proc` | builtin + Checkers | `get`, `executable`; `exec`, `run`, `spawn`, `wait`, `killer`, `kill`, `Child`, `Killer`, `Output`, `Stream`, `Streams`, `Spawned`, `pipe_end` | exist |
| `std.cown`, `std.future`, `std.actor` | builtin + Checkers | `Cown`, `new`; `Future`, `ready`; `Actor`, `new`, `send` | exist |

Not in the standard library: formats other than JSON, networking (`Net` waits for a program that needs it), command-line parsing, and anything else a package can provide.

### 16.4 Packages (D107–D109)

A package is a directory with `checkers.json`, its modules (`a/b.ck` is module `a.b`), and `checkers.lock`, which the build tool writes:

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
| `name` | yes | lower-case letters, digits and `_`, starting with a letter; not `std` |
| `version` | yes | `MAJOR.MINOR.PATCH` |
| `toolchain` | yes | the oldest `ckc` this package works with |
| `dependencies` | no | name → `{ "git": URL, "version": "MAJOR.MINOR.PATCH" }` (the oldest version that works, a tag `vMAJOR.MINOR.PATCH`) or `{ "path": DIR }`; the name is what this package imports it as |

An unknown field, a missing required one, or a malformed value is an error with its line and column in `checkers.json`. The lock file (D111):

```json
{
  "json_schema": { "git": "https://github.com/example/json_schema", "version": "1.4.0", "commit": "3f2a9c…" },
  "shared": { "path": "../shared" }
}
```

Minimal version selection: if this package needs `json_schema ≥ 1.2.0` and another dependency needs `≥ 1.4.0`, the build uses 1.4.0, even if 1.9.0 exists ("the highest required versions … are the minimum versions that satisfy all requirements", [Go modules reference](https://go.dev/ref/mod)). Lean's Lake records git dependencies the same way, with a revision per dependency in `lake-manifest.json` ([Lake reference](https://lean-lang.org/doc/reference/4.34.0/Build-Tools-and-Distribution/Lake/)).

`checkers build` in a package: read `checkers.json`, resolve and fetch the dependencies, write `checkers.lock`, then run `ckc build --package json_schema=~/.cache/checkers/packages/json_schema/3f2a9c… --package shared=../shared --uses .=json_schema,shared … main.ck` (D111).

Inside `json_schema`, its own modules are `validate`, `schema`, …; to this package they are `json_schema.validate`, `json_schema.schema`, and it can import only what its own manifest names (D111).
