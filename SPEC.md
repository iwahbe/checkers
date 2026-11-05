# Checkers — Language Specification

**Version:** 0.1 (draft) · **Last updated:** 11/05/2026 (rev. 2) · **File extension:** `.ck`

This document is the single source of truth for Checkers. Implementation follows the spec, never the other way around. Items marked **(proposed)** are Claude's recommendations awaiting Ian's veto; everything else is decided.

---

## 0. Decision log

| ID | Decision | Date | Status |
|----|----------|------|--------|
| D0 | Pillars: compile-time execution; dependent types + built-in prover; sealed module interfaces; functional + immutable; actors own concurrency & resources; interpreter first, Cranelift later; minimal Python/Haskell-ish syntax; types written only as constraints. | 11/05/2026 | decided |
| D1 | **Trust the SMT solver (Z3).** SMT-discharged obligations are accepted without certificate re-checking. Every use is recorded in a per-module *trust ledger* (§7.4) so certificate checking can be added later without changing the language. | 11/05/2026 | decided |
| D2 | Core calculus is **Quantitative Type Theory** with multiplicities {0, 1, ω} (Atkey 2018; as implemented in Idris 2). | 11/05/2026 | **(proposed)** |
| D3 | `Prop` is a definitionally proof-irrelevant, impredicative universe (as in Lean 4). | 11/05/2026 | **(proposed)** |
| D4 | The kernel knows only recursors (eliminators); pattern matching is compiled to them by the elaborator (Lean's approach). Keeps the trusted kernel small. | 11/05/2026 | **(proposed)** |
| D5 | Implementation language: Rust (Cranelift and the `z3` bindings are Rust-native). | 11/05/2026 | **(proposed)** |
| D6 | `Int` and `Nat` are arbitrary-precision (match SMT `Int` exactly). Fixed-width types are **refinements**, not separate number systems: `U8 = n~Nat, n < 256`, `I64 = n~Int, -2^63 <= n, n < 2^63`. Overflow is therefore a proof obligation, never a silent wrap; wrapping arithmetic is explicit (`wrapping_add`, …). `-` on `Nat` requires `a >= b`. The backend stores refined numbers in machine words. | 11/05/2026 (rev.) | **(proposed)** |
| D7 | Compile-time staging uses Two-Level Type Theory (Kovács 2022), added in milestone M6, not in the v0.1 core. | 11/05/2026 | **(proposed)** |
| D8 | **Haskell-style application.** Application is juxtaposition (`format x`, `List Int`, `Some b`) and every function is curried (`f x y == (f x) y`; partial application is ordinary). Operators are functions: `(+) 1 2 == 1 + 2`, with sections `(+ 1)` and `(1 +)`. `$` (lowest precedence, right-assoc.) and `.` (composition) behave as in Haskell. Declarations and applications now look the same. *Supersedes the 11/05/2026 parenthesized-call proposal.* | 11/05/2026 (rev.) | decided |
| D9 | **Constraint lists are the only place types are written:** function headers, constructor arguments, record fields, and refinement aliases all use `name~Type, predicate, ...` (§9.3). | 11/05/2026 | **(proposed)** |
| D10 | **Generics by auto-binding:** a lowercase name that appears free in a constraint and is not in scope becomes an implicit, erased (multiplicity 0) parameter. `fn map f xs -> ys : f~(a -> b), xs~List a` is generic in `a`, `b`. | 11/05/2026 | **(proposed)** |
| D11 | **Constructor and field invariants:** predicates in a constructor's or field's constraint list are part of the type. Building the value requires discharging them; matching on it provides them as hypotheses. | 11/05/2026 | **(proposed)** |
| D12 | **Refinement reflection inside a module:** total functions are reflected into the SMT logic (their definitions unfold on demand, Proof by Logical Evaluation). Outside the module only exported signatures, postconditions, and lemmas are visible (sealing, §6), unless exported `transparent`. | 11/05/2026 | **(proposed)** |
| D13 | **Proofs are code:** `lemma … ensures … proof`. In a proof, `match` is case analysis, a recursive lemma call is the induction hypothesis, `have L(args)` adds L's conclusion as a fact, `auto` hands the goal to the pipeline, `admit` skips (recorded in the trust ledger). A proof block (or match arm in one) may end with `have …`; the goal is then closed by an implicit `auto`. No separate tactic language in v0.1. | 11/05/2026 | **(proposed)** |
| D14 | `try e` propagates `Err`/`None` early, on `Result` and `Option`. A prefix keyword (extending to the end of the expression, like `$`) replaces the earlier postfix `e?`, which reads wrongly under juxtaposition: `f x?` would mean `f (x?)`. | 11/05/2026 (rev.) | **(proposed)** |
| D15 | **Interfaces** (type classes, Lean-style instance resolution) provide `==`, `<`, `+`, `format`, etc. Needed for D0's own example (`format x + y`). Detailed design deferred to its own section; until then the prelude's operators are built in. | 11/05/2026 | **(proposed, open)** |
| D16 | **Abstract type constructors declare parameter polarity** (`export abstract record Map k +v`). The module checks it internally; importers rely on it for strict positivity of nested inductives (e.g. a `Json` that contains `Map String Json`). | 11/05/2026 | **(proposed)** |
| D17 | `match` is first-match. Each arm sees the negations of earlier arms' patterns and guards as hypotheses. | 11/05/2026 | **(proposed)** |
| D18 | `==` inside constraints, `ensures`, and `check` is propositional equality and works on any type. In runtime code, `==` requires an `Eq` instance (D15), derived automatically for enums and records whose fields have one. | 11/05/2026 | **(proposed)** |
| D19 | **Literals.** `'x'` is a **byte** literal (`U8`): one ASCII character or an escape (`'\n'`, `'\\'`, `'\''`, `'\xff'`). `"…"` is a `String` literal; `"'"` is a one-character string. `b"…"` is a `Bytes` literal. Character (`Char`) literals are written `c'é'`. **(proposed: the `c'…'` form)** | 11/05/2026 | decided |
| D20 | **`String` is UTF-8**: an immutable byte sequence that is valid UTF-8 by construction (an invariant, D11). `Char` is a Unicode scalar value. | 11/05/2026 | decided |
| D21 | **Naming conventions, enforced by warnings:** keywords are lowercase; types, type constructors, and data constructors are `UpperCamelCase` (`Int`, `List`, `Json`, `Some`); top-level constants are `SCREAMING_SNAKE_CASE` (`MAX_DEPTH`); functions, variables, parameters, fields, modules, and type variables are `lower_snake_case`. Violations are warnings, not errors (codes W001–W005, §9.7). | 11/05/2026 | decided |
| D22 | **Spacing distinguishes `.` and `[`.** Glued (`v.stop`, `list.keys`, `src[i]`): field access, qualified name, indexing. Spaced (`f . g`, `f [x]`): composition, list-literal argument. Same rule as Haskell's `OverloadedRecordDot`. Field access and indexing bind tighter than application, so `Str s.value` is `Str (s.value)`. | 11/05/2026 | **(proposed)** |
| D23 | **Layout = Python-style logical lines** (§9.1): a newline ends a statement unless inside brackets, after a trailing `,` or binary operator, or before a line that starts with a binary operator or `:`. An indented block may follow any line that ends a header (`fn`, `enum`, `record`, `lemma`, `match`, an `if`/`else` line, a match arm ending in `->`, `proof`, `let x =`). | 11/05/2026 | **(proposed)** |
| D26 | **Two namespaces for `Uname`s, chosen by position.** After `~` in a constraint (and in a `type` alias's first constraint) a `Uname` resolves to a type; elsewhere it resolves to a data constructor or constant. So `enum Json` may have a constructor `Bool b : b~Bool`, and `record Error` is built with `Error pos kind` while its type is `Error src`. `lname`s share one namespace everywhere, so values used inside types (`Parsed Json src i`) work. This is Haskell's split, made sound for dependent types by D9 (types only ever appear after `~`). | 11/05/2026 | **(proposed)** |
| D27 | **Effects are linear capabilities** (§8.1–8.2). Effectful operations take an `own` capability and return a fresh one, so every function stays a mathematical function. `main` receives `sys~own System`, a record of capabilities (`term`, `fs`, `env`, `proc`, `net`, `clock`, `sched`). No `IO` monad and no effect system in the kernel. | 11/05/2026 | decided |
| D28 | **Droppable authority vs. linear resources** (§8.3). Authority tokens (`System`, `Term`, `Fs`, …, `Cown a`) are dropped implicitly when unused (the elaborator inserts `drop`); resources (`File`, `Child`, `Socket`) must be consumed explicitly. | 11/05/2026 | **(proposed)** |
| D29 | **`x <- f a c`** means `let (x, c) = f a c`, where the last argument `c` is an `own` variable (§8.4). | 11/05/2026 | **(proposed)** |
| D30 | **Concurrency is cowns + `when`** (behaviour-oriented concurrency, Verona; §8.5): race- and deadlock-free by construction, causal order, invariants as refinement types on contents. Actors and channels are libraries on top. *Supersedes the actors-with-session-types plan for M7.* | 11/05/2026 | decided (syntax **proposed**) |
| D31 | `main`'s signature: `fn main args sys -> code : args~List String, sys~own System, code~ExitCode`. `code` may also be a `Future ExitCode` (§8.6). The process exits once all scheduled work has finished. | 11/05/2026 | **(proposed)**; exit-after-all-work decided |
| D33 | **Nothing ever blocks.** No `await`. Effectful fork/join is `f <- fork using sched` and `r <- join x = f, … using sched`: both schedule a behaviour and return a `Future`; a join runs after the forks it names, by causal order (§8.6). | 11/05/2026 | decided (syntax **proposed**) |
| D34 | **`par (e1, …, en)`** evaluates the components of an n-tuple in parallel and returns the tuple. Pure only; to the prover `par t == t`. A keyword, not a function, because Checkers is strict: a function's arguments would already be evaluated, one after another, before it ran. | 11/05/2026 | decided |
| D32 | **Record patterns** `Ctor { a, b = p }` bind named fields; unnamed fields of a linear record are dropped (they must be droppable). | 11/05/2026 | **(proposed)** |
| D24 | **Development loop:** Claude owns the implementation; Ian drives with examples. An issue is "found X, expected Y" with a `.ck` snippet. Each one becomes a regression test under `tests/` *before* the fix lands, and the spec is updated first whenever the expectation changes the language. | 11/05/2026 | decided |
| D25 | **Milestones reordered for CLI tools first** (§10): a running interpreter with `IO` comes right after type checking, before the prover, so Checkers can be used to build its own tooling early. Capstone: an interactive shell with a small scripting language, with proofs of its correctness. | 11/05/2026 | decided |

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
    │                                     Runtime IR ──▶ tree-walking interpreter (v0.1)
    │                                                └──▶ Cranelift backend (M8)
```

Three components are trusted: the **kernel** (core type checker), **Z3**, and the **Rust compiler/runtime**. The elaborator, parser, and optimizer are untrusted: if they produce a wrong core term, the kernel rejects it.

---

## 2. Multiplicities

Every binder carries a multiplicity ρ ∈ {0, 1, ω}:

| ρ | Meaning | Checkers use |
|---|---------|--------------|
| 0 | Erased. May appear only in types and proofs; never exists at runtime. | Proofs, type arguments, ghost values |
| 1 | Linear. Used exactly once at runtime. | Resources owned by actors (handles, channels, capabilities) |
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

### 5.3 Recursion and totality
All code that may appear in types or proofs must be **total**:
- **Structural recursion** is compiled to recursors (D4).
- **Well-founded recursion** via the accessibility predicate `Acc` (required for merge sort, quicksort, etc.). The termination measure is a proof obligation like any other, so it can go to Z3.
- **Surface form:** `decreasing e` on the first line of a function body gives the measure. `e` is a `nat` or a tuple of `nat`s, compared lexicographically. Mutually recursive functions share one measure space; each call must strictly decrease it (worked example: `value`/`array`/`elements` in `examples/json.ck`).
- **Recursion through containers** (`map depth items` where `items` is a field of the value being recursed on) is accepted as structural. **(proposed)** The elaborator inserts the membership proof, as Lean's `List.attach` does by hand.
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
4. `export transparent` **(proposed)**: use sparingly; the body becomes part of the stable interface. Typical use: small definitional helpers that specifications are written in terms of (`list.keys`, `len`).

Background: Rossberg, Russo & Dreyer, *F-ing Modules* (JFP 2014) for sealing; Gratzer, Sterling et al., *Controlling Unfolding in Type Theory* for why sealing must live in conversion in a dependent setting.

---

## 7. Theorem prover

### 7.1 Obligations
Elaboration produces obligations `Γ ⊢ ? : φ` with `φ : Prop`. Sources: preconditions at call sites, postconditions, constructor/field invariants (D11), index bounds (`src[i]` needs `i < len src`), `nat` subtraction (D6), termination measures, `ensures` of lemmas, and `check` declarations.

Γ includes **path conditions**: the guards of enclosing `if`s, the patterns and guards of the current `match` arm plus the negations of earlier arms (D17), the left operand of a short-circuiting `and`/`or`, and every `have` fact in scope.

### 7.2 Discharge pipeline
Tried in order; first success wins:
1. **Compute:** if φ is closed, evaluate it at compile time (this is where compile-time execution and proving meet; every `check` takes this path).
2. **SMT:** translate Γ and φ to SMT-LIB and ask Z3 (§7.3). On `unsat` of ¬φ, insert `smt_trusted φ`.
3. **User proof:** a `lemma`'s `proof` block (D13), or `have` facts added before the obligation arises. Tactics come later.

On failure, the error shows the obligation, the hypotheses in scope, and Z3's counterexample model when one exists.

### 7.3 SMT fragment (v0.1)
Decidable fragment, following Liquid Haskell: quantifier-free linear integer arithmetic, booleans, equality, and uninterpreted functions. Mapping:

| Checkers | SMT-LIB |
|----------|---------|
| `Int`, `Nat`, `U8`, … | `Int` (+ range facts for refinements) |
| `Bool` | `Bool` |
| `==`, `<`, `+`, `-`, `*` by constant | native |
| `Bytes`, `String` | `Seq` (Z3 sequence theory) |
| enums, records, `List`, `Option`, `Result`, tuples | `declare-datatypes` |
| function `f` defined in this module | **reflected** (D12): `f`'s defining equation is instantiated where `f` is applied, Proof by Logical Evaluation (Vazou et al. 2018) |
| imported function `f` | uninterpreted, plus its exported postconditions; transparent exports are reflected |

Lemmas are not added automatically; `have` brings one in. **(proposed)** An `@auto` attribute on an exported lemma adds it to every query in importing modules (F\*'s SMT patterns), for very common facts only.

Anything outside the fragment is not sent to Z3; it falls through to step 3.

### 7.4 Trust ledger (D1)
Each compiled module records every `smt_trusted φ` it relies on (obligation, Z3 version, query hash). `checkers trust <module>` prints the transitive ledger. This is the only place Z3 enters the trust base, and the hook for future certificate checking.

`admit` (D13) is also recorded, as an unproven assumption. Development builds allow it; `checkers build --release` rejects any module whose transitive ledger contains one.

---

## 8. Effects, capabilities, and concurrency

Decisions D27–D34. Worked examples: `examples/wc.ck` (a CLI tool), `examples/log.ck` (cowns and `when`), `examples/parallel.ck` (`par`, `fork`, `join`).

### 8.1 Why capabilities, and why linear

Every Checkers function is a mathematical function: the prover relies on `f x == f x`. A side-effecting call such as reading a file would break that if it were an ordinary application. Checkers keeps it sound the way Idris 2 and Clean do: effectful operations take a **capability** with multiplicity 1 (`own`) and return a fresh one. The old capability is consumed, so the same call can never be made twice with the same arguments, and every effectful function remains a pure function of its inputs.

A capability is also an **authority**: code can only touch what it is handed. A JSON library that never receives an `Fs` cannot read files, and its type proves it.

### 8.2 The root capability and `main` (D27, D31)

```
export fn main args sys -> code : args~List String, sys~own System, code~ExitCode
```

The runtime calls `main` with the command-line arguments and the root capability. `System` is a prelude record of capabilities, all `own`:

| Field | Type | Authority |
|---|---|---|
| `term` | `Term` | stdin, stdout, stderr, terminal modes |
| `fs` | `Fs` | the file system |
| `env` | `Env` | environment variables, working directory |
| `proc` | `Proc` | spawning and signalling processes |
| `net` | `Net` | sockets |
| `clock` | `Clock` | time, sleeping |
| `sched` | `Sched` | creating cowns and scheduling behaviours (§8.5) |

A program takes the capabilities it needs with a record pattern; the rest are dropped (D28): `let System { fs, term } = sys`. Capabilities can be **attenuated**: `files.within dir fs` returns an `Fs` confined to `dir`.

`ExitCode` is an enum: `Success`, `Failure n` with `n~U8, n > 0`.

### 8.3 Dropping: authority vs. resources (D28)

The kernel's multiplicity 1 means *exactly once* (§2). Forcing every program to hand back every capability it was given would be noise, so types fall into two groups:

- **Droppable** (authority tokens: `System`, `Term`, `Fs`, `Env`, `Proc`, `Net`, `Clock`, `Sched`, and `Cown a`): if one goes unused, the elaborator inserts `drop x` at the end of its scope. The kernel still sees exact linearity.
- **Resources** (`File`, `Child`, `Socket`, …): must be consumed explicitly (`close`, `wait`, …). Forgetting one is a compile error. In the shell capstone this proves, for free, that every child process is reaped.

Droppability is the `Drop` interface (D15). Until interfaces land, the prelude fixes which built-in types are droppable, and user types are not.

### 8.4 Binding effectful results: `<-` (D29)

Effectful operations return `(result, capability)`, by convention with the capability last in both the arguments and the result. Threading by hand is noisy, so:

```
input <- terminal.read_all term
```

means `let (input, term) = terminal.read_all term`. The **last argument** of the call must be an `own` variable; it is rebound to the returned capability. `_ <- terminal.print_line "hi" term` discards a `Unit` result. Otherwise it is an ordinary `let`, so proofs see plain tuple-returning functions.

### 8.5 Concurrency: cowns and `when` (D30)

Data is immutable, so sharing it never races; parallel evaluation of pure code is always safe (`par`, §8.6). What needs coordination is a **resource or state shared by several concurrent tasks**: the shell's job table, the terminal. For that, Checkers adopts Verona's *behaviour-oriented concurrency* (Cheeseman et al., OOPSLA 2023):

- A **cown** (concurrent owner) wraps a value. `c <- cown.new v sched` creates a `Cown a`. The cown handle has multiplicity ω and may be freely shared; its *contents* are owned by the cown, and a linear value moved into a cown (e.g. a `Term`) is no longer available to the creator.
- A **behaviour** gets exclusive access to one or more cowns:

  ```
  when l = log, t = screen using sched
      _ <- terminal.print_line (format (len l)) t
      (l, t)
  ```

  This *schedules* the body, which runs once it holds all the listed cowns at once. Inside, `l` and `t` are the current contents, with full ownership, and the body evaluates to the new contents (a tuple, in the order listed; a single value for one cown). `when` is a statement: it consumes `sched` and rebinds it, like `<-`. The body receives its own fresh `sched`, so it can create cowns and schedule further behaviours.

Guarantees, by construction:
1. **No data races.** Contents are only reachable inside a behaviour holding that cown.
2. **No deadlock.** All of a behaviour's cowns are acquired atomically; there are no locks to order.
3. **Causal order.** Two behaviours that share a cown run in the order they were scheduled.

**Invariants.** A cown's content type can be a refinement (`type Log = entries~List String, len entries <= 100`). Every behaviour must return contents of that type, so it must re-establish the invariant: this is the lock-invariant rule of concurrent separation logic, enforced by ordinary type checking.

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
let (fs1, fs2) = files.split fs
a <- fork using sched
    files.read "a.txt" fs1
b <- fork using sched
    files.read "b.txt" fs2
done <- join x = a, y = b using sched
    combine x y
```

- `f <- fork using sched` + block schedules the block as a behaviour and binds `f~Future t`, where `t` is the block's type. Like `when`, it rebinds `sched`.
- `r <- join x = f1, y = f2, … using sched` + block schedules a behaviour that runs after every listed future has been filled. Inside, `x`, `y`, … are the plain values (moved out of the futures; each future can be joined once). It binds `r~Future t` for the block's result, so joins compose.
- A future is a cown that only its own fork or join can fill, and that fork/join is the first behaviour scheduled on it. A later join on that future is ordered after it (causal order, §8.5), so its value is always present: no `Option`, no waiting, no deadlock.
- Each concurrent branch needs its own capabilities. Droppable capabilities can be split (`files.split fs` consumes `fs` and returns two independent `Fs` tokens); resources such as an open `File` cannot be.
- A behaviour body receives its own `sched` and may fork, join and `when` further.
- A `fork`, `join` or `when` body may use `own` values from the enclosing scope (e.g. `term`); they **move** into the behaviour and are no longer available outside it.

**Ending the program.** The process exits once no scheduled work remains. If `main` returns a `Future ExitCode`, that future's value is the exit code; this is how a program whose result comes from a join reports it.

### 8.7 Other effects

- **Non-termination:** `partial fn` (§5.3). A `partial` function cannot appear in types or proofs.
- **Errors:** `Result` and `try` (D14). No exceptions.
- **Algebraic effect handlers** (Koka, Effekt): not planned. Capabilities and `Result` cover the needs so far, and handlers complicate the prover.

### 8.8 Proofs about effectful code (later)

Capabilities and cown contents correspond to separation-logic resources (Iris, F\*'s Pulse). M3–M5 prove pure code; specifications over capability state (e.g. "after `files.write p b fs`, `files.read p fs'` returns `b`") come with the shell capstone.

### 8.9 Staging (M6, D7)

Two universes, compile-time and runtime; `quote`/`splice` across them. Compile-time code generation is guaranteed to produce well-typed runtime code.

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

**Keywords:** `module import as export abstract transparent fn enum record type let lemma ensures proof have auto admit check match if then else try and or implies decreasing partial ghost own when using par`. `fork` and `join` are **contextual**: they are keywords only in `fork using …` and `join name = …` (right after `<-`), so `join` remains usable as an ordinary function name. `not` is an ordinary prelude function.

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
param       ::= [ '+' | '-' ] lname                          -- polarity only on abstract exports (D16)
alias       ::= 'type' Uname { lname } '=' constraints NL    -- first constraint must be `x~T`
lemma       ::= 'lemma' lname { lname } [ ':' constraints ] NL INDENT
                { 'let' pattern '=' expr NL } 'ensures' expr NL
                [ 'proof' NL INDENT block DEDENT ] DEDENT
const       ::= 'let' Uname '=' expr NL                      -- compile-time constant
check       ::= 'check' expr NL                              -- compile error unless true

constraints ::= constraint { ',' constraint }
constraint  ::= lname '~' [ 'ghost' | 'own' ] expr           -- typing
              | expr                                         -- predicate (Bool or Prop)

block       ::= { stmt NL } expr NL
stmt        ::= 'let' pattern '=' ( expr | NL INDENT block DEDENT )
              | 'have' expr                                  -- lemma application; adds its conclusion
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
| `x~own T` | linear: used exactly once (actor-owned resources) | `(x :1 T)` |
| predicate over inputs only | precondition | refinement on the inputs |
| predicate mentioning the result name | postcondition | return type `{r : R \| P}` |
| predicate in a constructor/field list | invariant (D11) | `Prop` field, erased |
| free `lname` in a type position, not in scope (`a` in `xs~List a`) | implicit type parameter (D10) | `{a :0 Type}` |

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

---

## 10. Milestones

Reordered (D25) so that Checkers can run CLI tools before the prover exists.

| # | Deliverable | Done when |
|---|-------------|-----------|
| M0 | Rust workspace; lexer with layout (§9.1); parser for §9.2; naming warnings (§9.7); source-span diagnostics; `checkers parse` / `checkers check` | `examples/json.ck` and every spec example parse; golden tests for errors and warnings |
| M1 | Elaborator + kernel: name resolution, QTT core (§4), enums/records, `match` → recursors, inference and implicits, structural termination | `Vec`, `List`, `Nat` programs type-check; contract tests for every §4 rule, including rejected programs |
| M2 | Erasure, interpreter, prelude, capabilities and `main` (§8.2–8.4: `Term`, `Fs`, `Env`, `Proc`, exit codes), implicit `drop` | `examples/wc.ck` runs |
| M3 | `Prop`, equality, refinements, Z3 pipeline, trust ledger, `check` | verified insertion sort |
| M4 | Modules, sealing, exported lemmas | sort module used from another module via its lemmas only |
| M5 | Well-founded recursion, lexicographic `decreasing` | verified merge sort; `examples/json.ck` checks |
| M6 | Two-level staging (`comptime`) | compile-time-generated specialized code |
| M7 | Cowns, `when`, `fork`/`join`, futures, `par`, multi-threaded scheduler; actor library | `examples/log.ck` and `examples/parallel.ck` run; stress tests show no races or deadlocks |
| M8 | Cranelift backend | M2–M7 test suites pass native |
| M9 | **Capstone:** interactive shell with a small scripting language, with proofs of its correctness (parser round-trip, evaluator semantics, job control protocol) | the shell runs its own test scripts |

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
- A report from Ian is "found X, expected Y" with a `.ck` snippet. It is added as a failing golden test first, then fixed. If Y changes the language, this spec is updated before the code.
- `UPDATE_GOLDEN=1 cargo test` rewrites `.out` files; every rewritten file is reviewed in the diff before committing.
