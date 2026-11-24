# Checkers — Language Specification

**Version:** 0.1 (draft) · **Last updated:** 11/05/2026 (rev. 2) · **File extension:** `.ck`

This document is the single source of truth for Checkers. Implementation follows the spec, never the other way around. Items marked **(proposed)** are Claude's recommendations awaiting Ian's veto; everything else is decided.

---

## 0. Decisions

A GitHub issue with the label `proposal` records each language decision. [DECISIONS.md](DECISIONS.md) holds the earlier decisions, D0–D186.

| State | Issue | Labels |
|-------|-------|--------|
| Proposed | open | `proposal` |
| Deferred | open | `proposal`, `deferred` |
| Accepted | open | `proposal`, `accepted` |
| Implemented | closed as completed | `proposal`, `accepted` |
| Declined | closed as not planned | `proposal` |
| Superseded | closed as completed | `proposal`, `accepted`, `superseded` |

- Only Ian adds `accepted` or declines a proposal.
- A pull request that implements a decision puts the rule in the numbered sections of this document. The issue holds the reason for the rule.
- The pull request that completes a decision says `Closes #N`. An earlier pull request for the same decision says `Part of #N`. CI rejects `Closes #N` for a proposal without `accepted`.
- To change a decision, open a new issue and add `superseded` to the old issue. Do not reopen the old issue.
- Cite a decision as `#N`, or as `Dn` for D0–D186. Nothing a Checkers user reads cites a decision.

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
Strict positivity is required: a type may not occur to the left of an `->` in a field of its own constructors, however many `->`s it is to the left of (D182); a field type computed by an `if` or a `match` is checked in each of its arms (D178). A recursive type must have a value: at least one constructor must not need a value of the type first (E0367, D183). Each inductive `D` generates constructors and one recursor `D.rec` (dependent eliminator) with ι-reduction. Example (`Vec`):
```
inductive Vec (A : Type ℓ) : Nat → Type ℓ
  | nil  : Vec A 0
  | cons : (n :0 Nat) → A → Vec A n → Vec A (n + 1)
```

**Dependent `match` (D63).** When the value matched is a variable that the expected type mentions, each arm is checked against the type with the variable replaced by that arm's constructor. So `fn go ps acc -> f : …, f~format_type ps` can return a `String` in the `[]` arm and a lambda in the `Str :: rest` arm. The types of the variables in scope that mention it are refined the same way (D173): in the `One` arm of `match s`, `x~futures s a` is a `Future a`; a variable whose refined type holds no resource may there be used freely. Types that still contain an unknown (`_`) are not refined.

**Cases that can't occur (D144).** A `match` need not cover a case the facts in scope rule out: each case left out is an obligation that it can't occur (§7.1), and E0240 if the prover can't show it. In a specification every case must be covered.

```checkers
fn head xs -> r : xs~List Int, xs != [], r~Int
    match xs
        x :: _ -> x
```

### 5.3 Recursion and totality
All code that may appear in types or proofs must be **total**:
- **Structural recursion** is compiled to recursors (D4). It is checked by **size change** (#109): each call relates each of the callee's parameters to the caller's, as a strict part of one (bound by matching on it, `<`), the parameter itself passed on unchanged (`=`), or neither. A group of functions that call each other is structural when every cycle of calls, composed, makes some parameter strictly smaller: composing `<` with `<` or `=` gives `<`, `=` with `=` gives `=`, and every composed cycle from a function back to itself that composes to itself has a `<` from a parameter to the same parameter (Lee, Jones and Ben-Amram, *The size-change principle for program termination*, POPL 2001). So a helper may pass its parameter on as it is (`walk t` → `through kids` → `walk_all kids` → `walk t2`, with `kids` a part of `t` and `t2` of `kids`), arguments may change places (`swap a b` → `swap b p`, `p` a part of `a`), and the order may be lexicographic (`lex a q`, `lex p b`). When no measure is written or guessed and a cycle isn't smaller, E0301 points at the call where the cycle loses what it recursed on (#124): first one that passes on no parameter and no part of one, then one that passes no strict part; a call passing a parameter on unchanged keeps it. It names the cycle. When a measure was guessed and none was shown smaller (D150), E0301 points, for the measure left unproved at the fewest calls, at the first unproved call in that same order.
- **Well-founded recursion** via a measure (required for merge sort, quicksort, etc.). The termination measure is a proof obligation like any other, so it goes to Z3 (D55). In the kernel this corresponds to recursion on the accessibility predicate `Acc` of `<` on `Nat` (lexicographic for tuples).
- **Guessed measures (D150):** with no `decreasing`, a function whose recursion isn't structural gets a measure guessed from its parameters' sizes and the distances its guards bound (`i < len src` gives `len src - i`), alone or in pairs, and checked by the prover; E0301 names those tried if none works. A parameter taken apart by sequence patterns (§9.8, #169) has `Seq.size` of it among them, so a function recursing on the rest of a `::` needs no `decreasing`.
- **Surface form:** `decreasing e` on the first line of a function body gives the measure. `e` is a `nat` or a tuple of `nat`s, compared lexicographically. Mutually recursive functions share one measure space; each call must strictly decrease it (worked example: `value`/`array`/`elements` in `stdlib/json.ck`).
- **Lemmas (#76, #104).** A lemma that uses itself (`have l …` in its proof) is a proof by induction and must terminate the same way: structurally, by a measure written as `decreasing e` on the first line of its `proof` (the measure is part of the proof; it may use the lemma's `let`s), or by one guessed as for a function. At each recursive `have`, the measure at its arguments must be smaller, given the facts there. An induction on a position (`decreasing len src - i`) follows a parser's own recursion. An instance's lemma gives its measure the same way, in its proof; a class's lemma, a statement only, has none.
- **Recursion through containers (#102).** A function value passed to a callee counts as called only with strict parts of the caller's parameter when the callee calls its function argument only with strict parts of another argument, and that argument is a parameter of the function being checked or a strict part of one. Where the callee's body is visible, as for anything else (§6: the same module, or exported `transparent`), its body shows it; across a module boundary, from a sealed function, only its signature does, so changing a sealed body never breaks an importer.
  - **From a body.** Explicit parameter `p` of `f` is called only with strict parts of parameter `e` when every use of `p` in `f`'s body that can run (not in a specification or proof) is either a call whose first argument is a strict part of `e` (a variable bound by matching on `e`), or `p` passed whole as an argument to a function that promises it in turn, with `e` or a strict part of it as the argument it promises about. Any other use (returned, stored, passed to a local function, called with anything else) promises nothing. Functions may pass their parameters to themselves or each other: the promises are the largest set that holds together. A parameter never used is never called, so it promises everything.
  - **From a signature.** A parameter of type `(x~A -> …, m … e … x …)` promises it for `e` when `m` is a **membership**: a predicate whose body shows it is `True` only where `x` equals (`==`, which compares structure) a strict part of `e`. A value equal to a part has the same structure, so it is just as small. A body shows it when every way to `True` passes through `y == x` with `y` a strict part of `e` (bound by matching on `e`, or a field of it), or through a membership (itself, recursively, or another) of `x` in `e` or a strict part of it; `False` never does, and anything else breaks it. `m`'s body must be visible, as for proofs (§6): a membership that is sealed doesn't count outside its module. `std.list.contains` is one, and a program's own containers have theirs (`holds t x` over a tree). `std.list`'s `all` and `map`, both `transparent`, make the promise with `contains` in their signatures (§16.3); so may a program's own functions. The function making the promise proves it keeps it: each call of its function parameter obliges the predicate there (D84), and passing the parameter on obliges the implication between the two refinements (D85).
  - **The function value** may be a bare name (`list.all walk kids`: the call `walk x`), a partial application (`list.map (by k) kids`: `by k x`, its first remaining parameter, D86), or a lambda (its parameter is the strict part).
  - **When it fails,** E0301 points at the function value passed and its help says why the function it is passed to isn't known to call it only with parts: its body uses the parameter another way; its body is sealed and its signature makes no promise (with an example precondition); its precondition's predicate isn't a membership; or that predicate is sealed.

  ```
  fn every xs p -> r : xs~List a, p~(a -> Bool), r~Bool
      match xs
          []        -> True
          x :: rest -> p x and every rest p

  fn walk t -> r : t~Tree, r~Bool
      match t
          Leaf      -> True
          Many kids -> list.all walk kids and every kids walk
  ```

  `list.all` promises it in its signature; `every`, in the same module, shows it in its body. An importer of `every` would need it exported `transparent`, or the promise in its signature.
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
   | `export abstract enum/record T a +b` | the type constructor and its parameter polarities only (D16): importers can't build one, match on it or read its fields (E0247, D155); only the functions its module exports can |
   | `export lemma` | statement only |
   | `export transparent fn` | everything, including the body (it unfolds in conversion and in the solver) |
   | an instance's `fn` | its signature: its own (§9.8), or else the class's at the instance's type (#249) |
   | an instance's `transparent fn` | everything, including the body, as for `export transparent fn` |
3. **Proofs are part of the interface.** Because bodies are sealed, a library must export the lemmas and postconditions its users need. A sorting module exports `sort` *and* `sort_sorted`, `sort_perm`. This is how libraries "ship with proofs."
4. `export transparent`: use sparingly; the body becomes part of the stable interface. Typical use: small definitional helpers that specifications are written in terms of (`list.keys`, `len`). The functions a transparent body calls that the module doesn't export are visible with it, or it would say nothing; so are those a `transparent` instance function calls. An exported function such a body calls stays sealed: importers see its signature only. An instance's dictionary is visible wherever the instance is used (which function a class's function is, at a known instance), but an instance's function is sealed like any other unless marked `transparent` (#249).

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
| type parameter condition (#136) | every application of a type whose parameters have predicates (`Ordered 5 1` for `record Ordered lo hi : lo~Nat, hi~Nat, lo <= hi`), wherever it is written: a parameter, the result, a field | the type's predicates, with the arguments substituted |
| weakened refinement (D83) | a value whose refinement is replaced by a weaker one in a covariant position (`List (n~Int, n >= 6)` as `List (n~Int, n >= 5)`) | for any `n`: the found predicates imply the expected ones |
| call of a function-typed value (D84) | `f a` where `f`'s type has preconditions | the preconditions at `a`; afterwards its postconditions at `a` and `f a` are facts |
| function passed as a value (D85) | a named function, partial application or lambda passed where a function type is expected | for any argument: the expected precondition implies the function's own; with it, the function's postcondition implies the expected one |
| refined type argument (D71) | a value checked against a refinement alias that the call or constructor it is passed to doesn't already check: one that comes from a type argument (`n` in `n :: xs : List Small`, `Some n : Option U8`, a list literal's elements, a tuple's components, a lambda's result). Not for a value whose type is already that alias, and not for an operand of an arithmetic or comparison operator (`10` in `x < 10` with `x~Small`) | the alias's predicates, with the value substituted |
| `Nat` subtraction (D6) | `a - b` on `Nat` | `a >= b` |
| division | `a / b`, `a % b` | `b != 0` |
| index | `src[i]` | `i < len src` |
| lemma | a `lemma` without a proof, or `auto` in a proof | its `ensures`, or the current goal |
| `have e` (D49) | a `have` of a `Bool` | `e` |
| case left out (D144) | each case a `match` (outside a specification) does not cover | the case can't occur: `False` from the facts there; E0240 if not proved |
| `check` | `check e` | evaluated (D40), no solver |

Inside types and specifications only two obligations are made: a called function's precondition (M17) and a type's parameter conditions (#136). Each predicate may rely on those written before it.

Γ, the **facts in scope**, contains: the preconditions of the enclosing function; the definitions of `let`-bound variables; `n >= 0` for every `Nat`; **path conditions**, namely the guards of enclosing `if`s (true in `then`, false in `else`), the left operand of a short-circuiting `and`/`or`/`implies`, the constructor equation of the current `match` arm (`xs == y :: rest`) together with that constructor's invariants, the literal of a literal arm or the negations of the others in its `_` arm, and an arm's guard; the `ensures` of every lemma brought in with `have`, and every `have` fact (D49); and the postcondition of every function applied in the goal or the facts (D50).

### 7.2 Discharge pipeline
Tried in order; first success wins:
1. **Compute:** a `check` is evaluated at compile time (D40).
2. **SMT:** translate Γ and ¬φ to SMT-LIB and ask the linked-in Z3 (§7.3, D46). On `unsat`, φ is proven, and the ledger records `smt φ` with the query's hash. First the full query with a small work limit (D154), whose answer is final when Z3 gives one: `unsat` proves φ, `sat` is a real counterexample. Where Z3 gives up, weaker queries, since `unsat` from a weaker query is still a proof (M12): (a) every reflected definition uninterpreted, fast when the facts in scope (`have`) already suffice; (b) only the definitions the goal mentions, so Z3 doesn't unfold functions whose results the facts give; (c) every definition, without the quantified postconditions of other functions; each with the small work limit, then those Z3 gave up on again with a larger one (D101), since giving up on one only means trying the next. Then (d) the full query with the full limit; if Z3 gives up on it, a counterexample from (c) with the full limit is shown. Z3's answers are cached (D100).
3. **User proof:** a `lemma`'s `proof` block (D13, D49), or `have` facts added before the obligation arises.

On failure (D48), the error shows the obligation, the facts in scope, and Z3's counterexample when one exists. A counterexample satisfies every fact in scope. A `forall` fact is not given to Z3 (§9.9), so where there is one, the counterexample is checked against it: the query is asked again with the `forall` facts given quantified (each variable over its type: a `Nat` is non-negative and a refinement's predicates hold), first with the counterexample's values fixed, then free. A model of it is shown; otherwise a note says there is no counterexample, because Z3's breaks a `forall` in scope or could not be checked against it (#77).

### 7.3 SMT fragment (v0.1)
Decidable fragment, following Liquid Haskell: quantifier-free linear integer arithmetic, booleans, equality, datatypes, arrays and uninterpreted functions. Mapping:

| Checkers | SMT-LIB |
|----------|---------|
| `Int`, `Nat`, `U8`, … | `Int`, with `n >= 0` for `Nat` and the alias's predicates for refinements |
| `Bool` | `Bool` |
| `==`, `!=`, `<`, `<=`, `+`, `-`, `*`, `/`, `%` | native (`div`, `mod`: Euclidean, like Checkers) |
| `Array a` (and `Bytes`, `Array U8`) | `(Seq S)` for `a`'s sort `S`; `len`, `a[i]`, `++` native; each `a[i]` is known to satisfy the element type's refinement (`< 256` for `U8`) (D133); what a sequence pattern leaves (`array_rest`, §9.8) is `seq.extract` from the second element, as the runtime's slice is (#232) |
| `String` | its UTF-8 bytes, `(Seq Int)` (D58): `len` (bytes, not characters), `++` and `utf8.encode` native; `s.bytes`, `String b` and a `match` on its constructor are the bytes themselves (#170). Every string's bytes satisfy `valid_utf8`, which is uninterpreted, and each byte or string literal in a query comes with whether it is UTF-8, so `string.bytes s != b"\x80"` is proved |
| `Bag` (D47) | `(Array Int Int)` |
| enums, records, `List`, `Option`, `Result`, tuples | `declare-datatypes`, with type parameters (value parameters are dropped from the sort); a value's constructor invariants are assumed, with the value parameters of its type filled in (`e~Error src` gives `e.pos <= len src`); a value has what its type says of its parts, one rule for tuples and datatypes (#156): a tuple's parts and a datatype's fields at refined types, or `Nat`, have their predicates, nested (`t~(Bool, (s~Nat, s > 3))` gives `s > 3` of its second part, and `p~Option (Pair Bool (s~Nat, s > 3))` of `p`'s `snd` where `p` is a `Some`), a field's type taking the type's arguments, types and values, and the fields before it, a constructor's fields and invariants under its tester; this holds of a local however a pattern takes it apart, of a field read, of an array element, and of a call's result's parts and fields where the callee's preconditions hold, the callee recursive or not; a value is looked into two datatypes deep and not again at its own type (a list's tail), a value deeper having its facts where the program names it (a pattern, a field read), an abstract type is not looked into, and a sealed function's result has what its signature says, not its body; a type whose values reach it again only through an array or a function (`Cells cells : cells~Array Grid`, `FromEmpty f : f~(Empty -> Absurd)`), which Z3 would refuse as not well-founded, gets one more constructor without fields that no program builds, and every value the query names (a parameter, a field, an array element) is known not to be it |
| type variables, abstract types | uninterpreted sorts |
| a parameter of function type | an uninterpreted function; if its type is refined, its postconditions hold at every application where its preconditions do (a pattern-guarded axiom, D139) |
| a function value (D139) | Z3's `(Array A B)`, curried (`Int -> Int -> Int` is `(Array Int (Array Int Int))`); applying it is `select`; a lambda, even one using local variables, is Z3's `lambda`, also where it is given to a function parameter inside a reflected body (`body xs (\ys -> fix body ys)`, #231), and a named function, a partial application or a function parameter passed as a value is one applying it; a known function argument (a named function, a lambda without free variables) still picks a specialized instance of a reflected function (D57), while a function Z3 can't see into (sealed, a builtin) takes it as a value, so a call in a body and the same call in a lemma are one term (#231) |
| function `f` defined in this module, or imported `transparent` | **reflected** (D12) as `define-fun-rec`, instantiated per type; Z3 unfolds the definition where needed |
| other imported functions, builtins | uninterpreted, plus their postconditions |
| `match`, `if`, `let` | `ite` on testers, `let` |

A sequence pattern (§9.8) is the `match` on `Seq.uncons`'s result it stands for: at a known instance its functions are the instance's (the prelude's `Seq` instances for lists, arrays and strings are `transparent`, so their bodies are visible everywhere), and at a clause `Seq s` `uncons` and `size` are uninterpreted, with `uncons`'s postcondition at each call.

Effects (`when`, `fork`, `join`) and functions of types (polymorphic function values) are outside the fragment (E0451); prove facts about them with a lemma.

Z3 sees more values than the program can build: `Option Nat` is `Option Int` to it, and neither a record's invariant nor a function's precondition is part of a sort. So a fact about all values of a type is assumed only where it holds for all of Z3's values too. A `Nat` result of `f` is assumed `>= 0`:
- at each call in the query, under `f`'s precondition, like a postcondition (for a class's function, the class's precondition, at a known instance too, §9.8);
- for every argument, including in terms Z3 creates by unfolding definitions, only if that holds for every solver value: `f` is not reflected (then it is free), or `f` has no precondition, recurses only structurally, and its body is built from non-negative parts (`0`, `1 + length rest`, other such functions). `max_of`'s `if x > m then x else m` is not such a body, so `max_of xs >= 0` is known only where `max_of xs` appears in the query; `have max_of xs >= 0` puts it there.

If Z3 rejects a query, which is a checkers bug, the obligation is reported unproven, never proven. A definition recursing by `decreasing` is given to Z3 only where its recursion ends (D118): `f x = if D then body else f#outside x`, where `D` is its `Nat` parameters being non-negative and, if its termination depends on them, its preconditions; elsewhere its value is unknown, so an equation such as `half 0 = 1 + half 0` (no solution) never reaches Z3. Calls in specifications must meet their callees' preconditions, as calls in bodies do, so a specification can't name a value no program computes. Each condition may rely on those written before it, as facts: in a function's signature, a constructor's list, and a record's fields, where the conditions of the fields before it come first (#108).

**Equal arrays** (#75). Z3 doesn't conclude that two sequences are equal from their elements, so an obligation whose goal is `xs == ys` on arrays (`Bytes` too) is also proved by `len xs == len ys` and `xs[w] == ys[w]` at a fresh index `w`, where `0 <= w < len xs`. A `forall` in scope over one variable of type `Nat` or `Int` is given at `w` (as at a `forall` goal, §9.9; not one over a refinement of them, which may not hold at `w`), so a lemma whose `ensures` is `forall k : k~Nat, k < len xs, xs[k] == ys[k]`, brought in with `have`, proves `xs == ys`. Only a goal that is the equality itself: for one inside `and`, `if` or another expression, `array.ext` and `bytes.ext` state the rule as lemmas.

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

**How it is checked.** An inline refinement is an anonymous alias, so D71's machinery applies unchanged: obligations where a value is built, variance through type arguments. What changes is the comparison of two refinements in one position: by implication for any value (D83), proven by Z3, where D71 asked for the same alias. A type's own declaration gives the variance of its parameters (covariant where strictly positive, as tuples' parts are), from where it is declared on, so `Pair Nat (j~Nat, i < j)` is a `Pair Nat (j~Nat, i <= j)` in its own module too (#156); an abstract type's marks are what importers and the rest of its module see (D16). For function types the comparison runs both ways (D85): preconditions contravariantly, postconditions covariantly. All of these are about one value or one argument at a time, so they need no induction.

A function type's precondition may mention a parameter of the enclosing function given after it, as `list.contains xs x` does in `fn all p xs -> r : p~(x~a -> Bool, list.contains xs x), xs~List a, r~Bool` (§9.3, #102). The function promises to call `p` only with elements of `xs`, and callers may pass a function that only accepts those.

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
| **Resource** | `File`, `Child`, `Pipe`, `Socket` | linear by type (D39): used exactly once, threaded with `let (x, r) = op r`, closed explicitly; `own` may be written | yes |

### 8.2 The root capability and `main` (D27, D31)

```
export fn main args sys -> code : args~List String, sys~System, code~ExitCode
```

`main` may also be a constant whose value has this type: `export let main = go` (D181). `main` can't have a precondition, because the runtime proves nothing about its arguments (E0366).

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

**Effect statements.** An expression whose result is `Unit` may stand alone as a statement line in a block, e.g. `terminal.print_line "done" term`. Only expressions returning `Unit` may: discarding any other value needs `let _ = …`.

### 8.4 Resources: linear, threaded with `let` (D29, D171)

A resource is an open, stateful thing that must be released: an open `File`, a `Child` process, a `Pipe`, a `Socket`. It has multiplicity 1, implied by its type (D39), and must be consumed exactly once, as must any value that contains one. A generic function accepts a resource only through an `own` parameter (`v~own a`, D45). Forgetting to `close` a file or `wait` for a child is a compile error, which proves, for free, that the shell reaps every child it spawns.

Operations on a resource consume it and return a fresh one together with their result, `(result, resource)`, with the resource last. A `let` takes the pair apart and rebinds the resource's name:

```
let (line, f) = files.read_line f
let (_, f) = files.write_bytes b f
files.close f
```

Because each operation consumes the previous token, the prover sees the operations in sequence; this is where ordering proofs about effects (§8.8) live.

Resources are created from authorities, e.g. `files.open path fs` returns `Result File IoError`.

**Streams (D112).** Every byte stream is a `File`: an open file, the standard streams (`terminal.stdin term`), and the pipes of a child process. The same operations read and write all of them:

```
let input = terminal.stdin term
let (header, input) = files.read_line input       # Content-Length: 52
let (body, input) = files.read_exactly 52 input   # (Result Bytes IoError, File)
files.close input

match proc.spawn "ckc" ["check", "--json", path] (Streams Discard Pipe Inherit) p
    Ok (Spawned child () out ()) ->           # out~File: only stdout is piped
        let (text, out) = files.read_rest out # (Result Bytes IoError, File)
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

- A **cown** (concurrent owner) wraps a value. `let c = cown.new v sched` creates a `Cown a`. The cown handle may be freely shared; its *contents* are owned by the cown, and it can't hold a resource (E0405, D156 k): its handle can be shared, so nothing would make sure what it held was closed. A resource stays with one owner, passed on through calls and the closures given to `future.fork` and `future.join`; a cown holds the rest of the state.
- A **behaviour** gets exclusive access to one or more cowns:

  ```
  when l = log, n = total using sched
      terminal.print_line format"{len l}" term
      (l, n + 1)
  ```

  This *schedules* the body, which runs once it holds all the listed cowns at once. Inside, `l` and `t` are the current contents, with full ownership, and the body evaluates to the new contents (a tuple, in the order listed; a single value for one cown). `when` is an expression of type `Unit`: its result reports only that the body has been scheduled, not that it has finished. The body may use authority capabilities from the enclosing scope (here `term`) and may schedule further behaviours with `sched`.

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

`par` takes a tuple literal with two or more components, evaluates them in parallel (work-stealing tasks), and returns the tuple. The components must be pure: no capabilities, no `partial` calls. Pure code holds no cowns and schedules nothing, so the implicit join is safe. A component may `future.join` a future (#57): it waits until the future is filled, like a behaviour's join. To the prover `par t` is `t`, so a parallel `sort` keeps its proof, stays a pure function, and can be used in types.

**Effectful: `fork` and `join` (D171, D176).** Functions of `std.future`:

```
let a = future.fork sched $ \_ ->
    files.read "a.txt" fs
let b = future.fork sched $ \_ ->
    files.read "b.txt" fs
let (x, y) = future.join (a, b)
combine x y
```

- `future.fork sched f`, `f~own (Unit -> t)`, schedules `f ()` as a behaviour and gives a `Future t`.
- `future.join x`, `x~own futures ts`, gives `values ts`: the value of a future, or the values of a tuple of futures (`futures (Then a (Last b)) = (Future a, Future b)`, `values` the same without `Future`; `ts` is worked out from `x`'s type, D175). If a future isn't filled yet, the behaviour parks until it is (§13.8), keeping its cowns. Each join gets the future's value, so a future may be joined more than once (D167 m **(proposed)**); a future of a resource must be joined exactly once (D156 l).
- `fork`'s function is one-shot (D171 c): it may use resources, which move into the behaviour.
- A future is filled only by its own `fork`, whose function holds no cowns. Such a function can wait only for futures that existed before it, so waits form no cycle: a `join` always ends, even in a `when` body (D176 c).
- Behaviour bodies may use authority capabilities from the enclosing scope (each use gets its own token, §8.3) and may fork, join and `when` further.
- A resource used inside a `when` body, or a closure given to `fork`, **moves** into the behaviour and is no longer available outside it. Two concurrent branches therefore can never share an open `File`.

**Ending the program.** The process exits once no scheduled work remains. If `main` returns a `Future ExitCode`, that future's value is the exit code.

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
    let acc2 = acc1 ++ (display age [])
    let acc3 = acc2 ++ " years old"
    acc3
```

with no format string left to parse at run time (`display` is `std.string`'s, §9.11). A bad placeholder is a compile-time error: its type is `BadPlaceholder`, so `fmt "{x}" name` reports too many arguments for a `BadPlaceholder`, and `fmt`'s precondition `valid (string.bytes s) 0` catches the rest.

---

## 9. Surface language

The worked example for this section is `std.json` (`stdlib/json.ck`; `examples/json.ck` uses it): an RFC 8259 parser and renderer whose bounds checks, termination, error positions, and object-key uniqueness are proven, plus a round-trip theorem. Decisions: D8–D23.

### 9.1 Lexical structure

**Logical lines (D23).** Source is split into logical lines, Python-style. A physical newline does **not** end a logical line when:
1. it is inside `(…)`, `[…]`, or `{…}`;
2. the line's last token is `,` or a binary operator (`+ - * / % ++ :: == != < <= > >= and or implies $ .` and the type operator `->` **inside brackets only**); or
3. the next line's first token is a binary operator from that list, or `:`. A sign is not a binary operator (D169): a line starting with `-1` starts a new logical line, at any indentation (a block's first line, a `match` arm `-1 -> …`), and one starting with `- b` continues.

A trailing `->` or `=` outside brackets does **not** continue the line; it opens a block (a match arm body, a multi-line `let`). Indentation uses spaces only; a tab in leading whitespace is an error. When a logical line is followed by a more-indented line, the lexer emits `INDENT`; on return to an enclosing level it emits matching `DEDENT`s (an inconsistent dedent is an error). A block indented past the continuation line that opens it (a `match` among a signature's constraints) belongs to that line: its lines are laid out from that line's column, and a line that returns from it to a column between the logical line's own and the block's opens the logical line's next block (`NEWLINE INDENT`: the function's body):

```checkers
fn pick o -> r : o~Option Int, r~Int,
                 match o
                     None   -> r == 0
                     Some x -> r == x
    match o
        None   -> 0
        Some x -> x
```

Blank and comment-only lines are ignored for layout.

**Comments:** `#` to end of line.

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
| `tag"…"` | its formatter's `Result` (§9.10) | `page"<p>{name}</p>"` |

**Keywords:** `module import as export abstract transparent fn enum record type let lemma ensures proof have auto admit check match if then else try and or implies decreasing partial ghost own comptime when using par`. `not` is an ordinary prelude function.

**Glued vs spaced (D22):** `.` and `[` with no whitespace before them, directly after an identifier, `)` or `]`, are field/module access and indexing. With whitespace before them they are composition and a list literal. **A sign (D169):** a `-` with white space, the start of the file, `(`, `[`, `{` or `,` before it, and glued to what follows (not white space, a closing bracket or `,`), is a sign: `-1`, `f -x`, `[1, -2]`. Every other `-` is subtraction: `a - b`, `a-b`, `- b`. A `-` where no operand comes before it (`2 * - 1`, `(- x)`) still negates.

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
alias       ::= 'type' Uname { lname } '=' constraints NL    -- first constraint must be `x~T`; parameters typed by use (D168)
lemma       ::= 'lemma' lname { lname } [ ':' constraints ] NL INDENT
                { 'let' pattern '=' expr NL } 'ensures' expr NL
                [ 'proof' NL INDENT [ 'decreasing' expr NL ] block DEDENT ] DEDENT
const       ::= 'let' Uname '=' expr NL                      -- compile-time constant
check       ::= 'check' expr NL                              -- compile error unless true

constraints ::= constraint { ',' constraint }
constraint  ::= lname '~' [ 'ghost' | 'own' | 'comptime' ] expr  -- typing; in a type, '(' constraints ')' is a refinement and
                                                                --   '(' [lname '~' ['own']] expr '->' [lname '~'] expr { ',' expr } ')' a refined function type (D82, D172 b)
              | expr                                         -- predicate (a Bool expression)

block       ::= { stmt NL } expr NL
stmt        ::= 'let' pattern '=' ( expr | NL INDENT block DEDENT )
              | 'have' expr                                  -- lemma application; adds its conclusion
              | 'have' lname '~' type                        -- a typing (D170)
              | expr                                         -- D35: must have type Unit
expr        ::= 'when' lname '=' expr { ',' lname '=' expr } 'using' lname NL
                INDENT block DEDENT                          -- schedules a behaviour; type Unit
              | 'if' expr 'then' expr 'else' expr
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
postfix     ::= atom { '.' lname | '[' expr ']' | template } -- glued only (D22)
template    ::= '"' { text | '{{' | '}}' | hole } '"'        -- glued to a lower-case name (§9.10)
hole        ::= '{' [ expr ] [ '|' expr { ',' expr } ] '}'
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
| predicate over a type's parameters (`record Ordered lo hi : lo~Nat, hi~Nat, lo <= hi`) | condition on the type (#136): an obligation wherever the type is applied (§7.1), a fact in its fields | erased |
| free `lname` in a type position, not in scope (`a` in `xs~List a`) | implicit type parameter (D10); a name used as a qualifier (`future` in `future.Future`) is never auto-bound | `{a :0 Type}` |

A constraint is only required where inference fails; `fn is_ws b : b~U8` infers its `Bool` result.

**Refinements may mention later parameters (#102).** A predicate in a parameter's type, at any depth (a function-typed parameter's precondition, an element type's refinement), may mention any parameter of the function, earlier or later: `fn all p xs -> r : p~(x~a -> Bool, list.contains xs x), xs~List a, r~Bool`. Only the predicates may: the rest of the type may mention only earlier parameters (a later one is E0204). The parameter's type without those predicates is its type in the function's core type (§3); with them, it is its type in the body and at a call:

- In the body, the parameter has its full type, so calling `p y` obliges `list.contains xs y` (D84).
- At a call with every argument the predicates mention, those arguments are checked first, then this one against its full type with them put in (`list.all walk kids` checks `kids`, then `walk` against `(x~Tree -> Bool, list.contains kids x)`). A function argument with no precondition is accepted (D85).
- At a partial application without one of them (`list.all p`), or where a later parameter's type depends on this one, the argument is checked against its type without the predicates, which asks more of it: it must accept any value of its base type.
- The function used as a value (D85) has its core type, the parameter's type without the predicates.

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

Every binary operator `op` is also the function `(op)`, curried. Inside a match guard `->` ends the guard, so a function type there needs parentheses. `f -1` applies `f` to `-1`, the `-` being a sign (D169); `f - 1` and `f-1` subtract. A sign negates the argument it is glued to (`f -x.y` is `f (-(x.y))`); at the start of an expression it negates the application after it (`-f x` is `-(f x)`). In patterns `-1` is a literal (`Num -1 -> …`). `a[i]` requires `i < len a`; `/` and `%` require a non-zero divisor. `==` follows D18.

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
| `(a, b, …)` | tuple | core Σ type; taken apart with patterns (`let (a, b) = p`) |
| `Option a` | enum | `None`, `Some x` |
| `Result a e` | enum | `Ok x`, `Err x`; works with `try` |
| `List a` | enum | `[]`, `x :: xs`, `[1, 2]` |
| `Bytes` | `Array U8` (D133) | `b"…"`; packed, one byte per element |
| `String` | record (#170): `bytes~Bytes, valid_utf8 bytes` | valid UTF-8 (D20); stored as its bytes (§14), so `s.bytes` and `string.bytes s` cost nothing; `String b` needs `valid_utf8 b`. Where a type is expected, `String` is the type, not its constructor |
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
| W020 | a declaration nothing used reaches (D144) |
| W021 | a `match` arm that earlier arms already cover (D144) |
| W022 | a branch that never runs: the facts there contradict each other (D144) |
| W023 | a constructor nothing used builds (D144) |
| W024 | a record field nothing used reads (D144) |
| W030 | a documentation link (`[name]`) that names no symbol in scope (D148 c) |
| W031 | a documentation link to a symbol that isn't exported (D148 c) |
| W032 | a code block in documentation that doesn't compile cleanly: each of its diagnostics, at its place (D148 d) |
| W033 | a `compile_fail` block that compiles, or fails with another error than it names (D148 d) |
| W034 | a code block whose `main` doesn't exit with `Success` (`checkers doc` and `checkers site`, D148 d) |

Used means reached, through any reference, from the roots: `main` and the exports of every module of the program, with an exported type's constructors and fields; every declaration of a root module with neither `main` nor an export; and always every `check`, lemma and instance (D144, #95). A program can also be a library: what its modules export counts as used, whether or not `main` uses it. The standard library and dependencies are not reported, and none of these is reported while there is an error in the names and types phase (a name that failed to resolve would look unused).

### 9.8 Classes and instances (D136, M23–M25)

```checkers
class Ord a
    fn le x y -> r : x~a, y~a, r~Bool
    lemma trans x y z : x~a, y~a, z~a, le x y, le y z
        ensures le x z

instance Ord (List a) : Ord a
    fn le xs ys
        …
    lemma trans xs ys zs
        proof
            …

fn larger x y -> r : Ord a, x~a, y~a, r~a, le x r and le y r
```

- **A class** lists functions (a signature, with a type for each parameter and the result, E0362; a parameter may be `own` or `ghost`, as in any signature, and its field in the dictionary takes it the same way) and lemmas (a statement); `C.f` names one. A member's parameter of type `ghost Type` with the name of the class's parameter *is* that parameter, passed explicitly (#161): `fn try_from x t -> r : x~s, t~ghost Type, r~Option t` is used as `try_from "123" Int`. It isn't in the dictionary (it is erased, and the dictionary is already for that type); in an instance the member writes it like any other parameter (E0365), and there it is the instance's type. Any other parameter (or result) can't have the name of the class's parameter, which its signature already uses (E0369). A function may have class clauses of its own (`fn weigh by xs -> n : Seq s, by~w, xs~s, n~Int`): its field in the dictionary takes their dictionaries as implicit parameters, so each call passes them, found where it is called, and an instance's function has them as any function with a clause does; the instance needs no context for them (#189). A lemma that follows from them is written outside the class, as an ordinary lemma with the clause `C a`.
- **An instance** gives each function a body (E0364 if one is missing, E0365 if its parameters don't match, E0363 for one the class doesn't have) and may give each lemma a proof, whose first line may be `decreasing e` (§5.3); without one, Z3 proves it. A function's signature is the class's, at its type, unless it writes one of its own (below); a lemma's statement is always the class's. Inside an instance a member's name is the instance's own (recursion on the type is ordinary recursion, checked for termination); the class's function at another type is `C.f`. Using the class's function at the instance's own type from inside it is recursion through the dictionary, which can't be checked (E0301). A class its functions use at the instance's variables is the instance's context (`instance Ord (List a) : Ord a`); without it, E0284's `help:` says to add it there (#189).
- **A signature of its own (#225).** An instance's function may write an ordinary signature, to promise more than its class, or require less, where the instance is known:

  ```checkers
  class Size a
      fn size x -> n : x~a, n~Int

  instance Size (List a)
      fn size xs -> n : xs~List a, n~Int, n >= 0
          match xs
              []        -> 0
              _ :: rest -> 1 + size rest

  fn known xs -> r : xs~List Int, r~Int, r >= 0
      Size.size xs                # the instance's postcondition
  ```

  - **Its shape is the class's.** The same parameters, in order, each `own` or `ghost` as in the class, a parameter for the class's `t~ghost Type` one (#161) written `t~ghost Type` (where it is the instance's type, as in the body; E0365 for another type), and the class's class clauses; the types are the class's at the instance's type, up to refinement: `n~Nat` for the class's `n~Int` is allowed (`Nat` is `Int` refined), `n~Bool` is E0365, at the type, with the class's declaration as a note. The names are the instance's own. Its context is the instance's, written in its header; a clause of the context written in the signature too is the same clause. A class's type (`Options`) is the instance's, as in the class's signature at the instance.
  - **It refines the class's**, checked by the prover as a refined function type is (§7.5): preconditions contravariant, postconditions covariant. For any values of the class's parameter types, the class's preconditions imply each of the instance's (E0371 at the instance's precondition otherwise: a call through the class needn't establish it); and where the class's preconditions hold, the instance's preconditions and postconditions imply each of the class's postconditions, a refinement of the result's type included (E0371 at the instance's signature otherwise, naming the class's condition; `n~Int` for the class's `n~Nat` doesn't promise `n >= 0`). Refinements inside the types are compared too, as §7.5 compares them, at any depth (a type argument by its variance, a tuple's part, a function type's parameter and result): a parameter's type in the class must imply the instance's, and the result's type in the instance must imply the class's, where the class's preconditions hold. Where both have a refinement in the same place, the prover shows the implication (E0371 at the instance's type otherwise, with what it needs and a counterexample: `r~(Int, (n~Int, n > 1))` for the class's `(Int, (n~Int, n > 2))`). Where only the type that must be implied has one, no proof can give it, because a refinement inside a type is never gained from an existing value: E0371 without the prover (`r~Option Int` for the class's `r~Option Nat`; `xs~List Nat` for the class's `xs~List Int`, which a caller through the class may pass `[-7]`; `f~(Nat -> Nat)` for the class's `f~(Nat -> Int)`). As in §7.5, a function type's own parameter is the exception: there the comparison is an obligation for any value, so `f~(Int -> Nat)` for the class's `f~(Nat -> Nat)` is E0371 with the counterexample `-1`. Each E0371 has the class's declaration as a note, and a counterexample when there is one. A signature identical to the class's is allowed, with no warning.
  - **The body is checked against it**, so the stronger promise is proved once, where the instance is (E0450 at the instance's postcondition).
  - **At a known instance** (the call's dictionary is that instance's, as for the direct call, §14, and in the prover), a call checks the instance's preconditions instead of the class's and assumes its postconditions, and the class's where the class's preconditions hold. The call's type is the class's result type, which the class promises only where its preconditions hold: so where the instance's result type lacks a refinement the class's has (`r~Int` for the class's `r~Nat`, or one inside it), the call must have it, from the class's preconditions holding at the call or else from the instance's signature at its arguments (E0450 at the call otherwise; under a recursive type, only the class's preconditions will do). With `fn pos w x -> r : w~a, x~Int, x > 0, r~Nat` in the class and `fn pos w x -> r : w~Box, x~Int, r~Int, x > 0 implies r >= 0` in the instance, `pos b 5` is a `Nat` and `pos b (-5)` is E0450, "cannot prove that `pos b (-5)` is a `Nat`"; with the instance's `r~Nat` instead, both are `Nat`s. Its body is visible to the prover as any instance function's is: in its module, or everywhere if it is `transparent` (below). Whether a dictionary is known is decided once the module's bodies are checked, so it doesn't matter where the instance is declared. A partial application of the class's function, or the class's function as a value, at a known instance has that instance's signature as a refined function type (§7.5, #252): `count 0` at `List Int`, with `fn count k xs -> n : k~Int, xs~List a, n~Int, n >= k`, is `(xs~List Int -> n~Int, n >= 0)`. Its result type is the instance's too: with the instance's `r~Int, x > 0 implies r >= 0` for the class's `x > 0, r~Nat`, `let f = pos b` gives `f (-5)` as an `Int` (E0450 where a `Nat` is needed) and `f 5` as a `Nat`, from the instance's postcondition. Its preconditions about the arguments given are checked where it is written; passed as an argument, it is compared with the parameter's type as any function is (preconditions contravariantly, postconditions covariantly); called, its preconditions are obliged and its postconditions are facts there. A value checked against a type is compared once the instances its types choose are found; one whose instance isn't known where it is written (`let f = count 0`, its type known only from a later call) has the class's signature for the parameters it still takes, and each call of it is a call of the class's function, with the instance's postconditions. Through a clause's dictionary, the class's signature.
  - **Generic code** (a dictionary from a clause, or an instance's context) sees only the class's signature: adding a signature to an instance never changes what a generic caller may assume or must establish.
  - **Lemmas** are unchanged: their statements are the class's at the instance; a proof may use the instance's stronger postconditions.
  - **At run time** nothing changes: the dictionary holds the instance's function, which a known call calls directly.

- **Sealed by default (#249).** An instance's function is sealed outside its module, as any function is (§6): an importer's proofs know its signature (its own, or the class's at the instance's type) and not its body. `transparent fn` in an instance makes the body visible to importers, with the functions it calls that its module doesn't export, as `export transparent fn` does; `transparent` on an instance's type or lemma is E0105. In its own module an instance's function is visible without the modifier. Its dictionary is always visible, so a known instance is always known; only what its functions do is sealed. Run time is unchanged: the direct call and specialization still call the instance's function. Where an importer's proof needs what a body does, prefer a signature of the instance's own (above) to `transparent`, unless the body is the natural specification (`le x y` is `x <= y`). In the standard library, these are `transparent`: the prelude's `Ord`, `Add`, `Sub`, `Mul`, `Neg`, `Monoid`, `Functor` and `Seq` instances, `Functor Array`, `Token Int Int`, and `std.json`'s `Token` and `Seq Tokens` instances.

- **Coherence.** An instance is for a type constructor applied to distinct variables (E0281), of the class's kind (E0286). A tuple type `(a, b)` counts, and so does `()` (its constructor takes no parameters, as `Bool`'s doesn't), written `()` or `Unit`; any other alias is E0281; its context is classes of those variables. A tuple's type constructor is the pair (D174): `instance C (a, b)` covers every tuple of two or more parts, `b` being the rest, so `(1, 2, 3)` uses it with `b` as `(Int, Int)`; an instance for `(a, b, c)`, which is `(a, (b, c))`, is E0281 (#130). It is declared in the package of the class or of the type (Rust's orphan rule, E0282). No two instances of a class have the same type constructor (E0283). An instance is visible wherever its module is loaded.
- **Using a class.** A clause `C t` in a signature is an implicit parameter, the dictionary. `t` may be a parameter `t~ghost Type` passed explicitly (#161): the dictionary is then an implicit parameter right after `t`, found once the type passed is known. A partial application that hasn't reached `t` has the clause in its type, `(t~ghost Type) -> {Parse t} -> Option t`, as any function taking a `ghost Type` does with what follows it. Each use of a function with such a parameter finds it once the types are known: a dictionary in scope (a clause of the enclosing function) for that class and type, or the instance for the type's constructor, with its context found the same way (E0284 if there is none, E0285 if the type isn't known). Only instances build dictionaries (E0287).
- **At a refinement alias** (#226). A class used at a refinement alias `T` of a type `B` (`Make Nat`) runs `B`'s instance (`Make Int`'s), which is valid only where that instance gives `T`'s values: E0456 at the use otherwise, whose `help:` suggests using `B` instead. An instance for an alias itself is E0281, whose `help:` says this. Only a value of the class's type the instance *gives* needs it; a value it is given needs nothing, as a `T` is a `B`.
  - **Results.** At a call of the class's function whose dictionary is that instance's (`make (-1)`, or `Read.read 5 Nat` passing the type explicitly), each value of the class's type in the result (the result itself, or one inside it: `Some`'s, a tuple's part, a field) must be a `T`, from what the prover knows at that call: the instance's signature at the call's arguments (§9.8's "A signature of its own") and its body where that is visible (in the instance's module, or where it is `transparent`, below). So `make (-1)` at `Nat` is E0456, "cannot prove that `make (-1)` is a `Nat` (`(make (-1)) >= 0`)", unless `Make Int`'s `make` promises `r >= 0`; with `Some v -> v == x`, `Read.read 5 Nat` gives a `Nat` and `Read.read (-1) Nat` doesn't. A part of the result a finite walk doesn't reach, one under a recursive type (`List t`, `Tree t`, the whole of it) or a function (`Int -> t`, `Option (Int -> t)`), is checked as one, from the instance's signature: its type for the part, at the call's arguments, must imply the class's at `T`, as a refined type does (§7.5; for a function, D85's comparison): `r~Tree Nat` for `Tree t`, `r~(x~Int -> y~Int, y >= 0)` for `Int -> t`. A list may instead be promised element by element with `std.list.all`: for `List t` the obligation is `list.all (\n -> n >= 0) (several 3)` (each element's predicates at `T`, joined by `and`), which `list.all (\x -> x >= 0) r` in the signature gives (the prover compares the two functions by what they return; `all` is `transparent`, so the instance's body proves it from `all`'s). Otherwise the use is E0456, "cannot prove that `several 3` has type `List Nat`", whose `help:` names both promises. Another recursive type has no such predicate: only its type promises it.
  - **As a value** (#252). The class's function used as a value or partially applied is checked where the value is finally used: compared with the function type expected there (`list.map make xs` at `List Nat`: wherever `list.map` may call it, the instance's postcondition makes its result a `Nat`; `list.map make [-1]` is E0450 there), or, for a local defined as one (`let f = make`), at each call of it as at a call of the class's function (`f 5` at `Nat` is accepted when `make` promises `u >= 0 implies r >= 0`). Compared with a type, it has the instance's signature (§9.8's "A signature of its own") where that instance's function has one of its own; otherwise, and where it is used other than as a call or against a type, it is checked through the dictionary.
  - **Through the dictionary.** Anywhere else the dictionary goes (to a function with the clause `C a`, a value checked as above, an instance's context such as `Make (List a) : Make a` at `List Nat`), generic code may call any of the class's functions with any arguments its signature allows at `T`: for each of them, wherever the class's preconditions hold, with its parameters of the class's type `T`s, its result's values of the class's type must be `T`s. So `larger x y`, of two `Nat`s, is a `Nat`: `Ord`'s functions give no value of the class's type; `made 1`, with `fn made u -> r : Make t, u~Int, r~t`, is E0456 unless `Make Int`'s `make` promises `r >= 0` for every `u`.
  - **Function parameters.** A parameter of a function type that takes the class's type (`f~(t -> Bool)`) is called by the instance with values it gives, and one that takes a function giving it (`f~((Int -> t) -> Bool)`) is given such a function by the instance. The class's type for the parameter at `T` must imply the instance's own type for it, as a refined function type does (§7.5: preconditions contravariant, postconditions covariant), at any depth, with a refinement written as an alias or inline: `f~(Nat -> Bool)` and `f~(x~Int -> Bool, x >= 0)` take only `T`s; `f~((x~Int -> y~Int, y >= 0) -> Bool)` is given only functions whose results are `T`s. Else the use is E0456, at a call as through the dictionary.
  - A refinement alias inside a type argument (`U8` in `Seq (Array U8)`) is the instance's variable, which it is generic in: nothing is checked, unless the instance's context uses the class at it (`Make (List a) : Make a`), where it is checked as above.
  - The instance's body counts only where the prover sees it: outside the instance's module, a sealed instance function (the default) is known by its signature alone, so `make 5` at `Nat` with `make u = u` and no signature is E0456 there, and accepted if `make` is `transparent`.
- **At run time** a dictionary is a record of the class's functions, passed as an argument; lemmas are erased.
- **In the prover** a class's function reading an unknown dictionary is a field of it, uninterpreted; with a known instance's dictionary it is that instance's function: inside the instance's module its body is visible, as any function's is; outside it, the function is sealed (§6): the prover knows its signature (its own, or the class's at the instance's type) and its body only if it is marked `transparent` (#249). A class's lemma is assumed for every dictionary, as each instance proves it; it is used with `have C.l …` (or `have l …`).
- **Termination.** Using an instance of the same module is a call of the function building its dictionary, which calls its functions and lemmas, so recursion through a dictionary is found like any other.

**Operators (M24).** On numbers, `+ - *`, negation and comparisons are built in, as before. On a type with an instance of the prelude's `Add`, `Sub`, `Mul`, `Neg` or `Ord` (or a type parameter with such a clause), `x + y` is `add x y`, `-x` is `neg x`, `x <= y` is `le x y`, `x >= y` is `le y x`, `x < y` is `not (le y x)` and `x > y` is `not (le x y)`. With no instance, the error is as for numbers (E0210). `Monoid` adds `zero` and the lemmas `assoc`, `zero_add`, `add_zero` (stated with `+`, so each needs `Add a`). `Int` has instances of all of these, so generic code works at numbers.

**Classes over type constructors (M25).** A class's parameter is a type constructor when its members apply it to arguments: in `class Functor f`, `xs~f a` makes `f` of kind `Type -> Type`. An instance is then for a type constructor short of that many parameters (`instance Functor List`, `instance Functor (Pair k)`; E0286 otherwise). A class's function may have type variables of its own (`a`, `b` in `fmap`), each an implicit parameter of its field in the dictionary. Any auto-bound type parameter applied to arguments is a type constructor in the same way (D10). `f a` is matched against `List Int` with `f` as `List` and `a` as `Int`. A recursive type may not be the argument of a type constructor parameter (E0354): `f` could use it to the left of an `->`. In the prover, at a type constructor parameter, `fmap` is a function Z3 knows nothing about but what `have Functor.fmap_id xs` and `have Functor.fmap_comp g h xs` give.

```checkers
class Functor f
    fn fmap g xs -> ys : g~(a -> b), xs~f a, ys~f b
    lemma fmap_id xs : xs~f a
        ensures fmap (\x -> x) xs == xs
    lemma fmap_comp g h xs : g~(b -> c), h~(a -> b), xs~f a
        ensures fmap (\x -> g (h x)) xs == fmap g (fmap h xs)

fn doubled xs -> ys : Functor f, xs~f Int, ys~f Int
    fmap (\x -> x * 2) xs
```

**A class's types (#133).** A class may declare a type, `type Name`, that each instance gives: it names a type that depends on the class's parameter. Inside the class, its functions and lemmas use it by its bare name, anywhere a type may appear (a precondition's predicate too). It takes no parameters of its own (E0124). `type Name = T` gives it a default, which may not mention the class's parameter (E0288), so it means the same at every instance.

```checkers
class Display a
    type Options = NoOptions
    fn display x os -> s : x~a, os~List Options, s~String

enum NoOptions                        # no constructors: the only list of them is `[]`

instance Display Money
    type Options = MoneyOption
    fn display m os
        …

instance Display Int                  # its `Options` is `NoOptions`
    fn display x os
        …

instance Display (Pair a) : Display a
    type Options = Display.Options a  # may use its context's types
    …
```

- **An instance** gives it with `type Name = T`, or leaves it out to take the default; with no default, leaving it out is E0364, and giving a type the class doesn't have is E0363. In the instance's signatures, `Name` is that type. A class's function used in them (in a precondition, say) finds its instance from its arguments, as anywhere; where they don't tell (`valid os`, `os` a list of options), it is the instance's own (#146).
- **Using it.** Outside the class it is `C.Name t` (`Display.Options Money`; `C.Name` alone is E0291). At a type whose instance is known it **is** the instance's type, both when types are compared and in the prover: `display price [Cents]` checks, and a `match` on `Cents` with it. Its refinement comes with it: `Seq.Elem (Array U8)` is `U8`, so the first element `Seq.uncons` gives is known to be `< 256`, as in a `x :: rest` pattern. At a type parameter `a` with the clause `C a`, it is a type of its own, equal only to itself: generic code can pass `[]`, or values it was given at that type, and what its constraints (below) allow, and nothing else. Without a clause for `a` it is E0284, as for a class's function.
- **It doesn't determine the class's type.** `Int` and another type may both have `NoOptions`. So comparing `C.Name a`, while `a` isn't known yet, with another type neither fails nor guesses: it waits until `a` is known (from another argument, or a later use of the same value), and is then compared again; if `a` is never known, the use is E0285. `(\v -> display v [Cents]) (Money 1250)` checks.
- **In core** the dictionary is a record whose fields may depend on earlier fields: its types first (`$Options~ghost Type`), then the dictionaries of their clauses (below), then its functions, whose types use them. `C.Name t` is a definition reading that field of the dictionary found for `t` (Lean's classes, structures with fields of type `Type`, work so).
- **At run time** the type is erased, but the dictionary keeps its layout word (D133), as a type argument's slot does, so generic code lays out an array of `C.Name a` as the instance's type is laid out.
- **In the prover** a known instance's type is that type. At a dictionary in scope for `t`, it is a sort of its own applied to `t`'s sort (`Display.Options a`): one instance per type, so two uses at the same type are the same sort.
- **Cycles and positivity.** An instance's type defined through itself, directly or through other instances (`type Options = Display.Options Money` in `Money`'s instance), is E0225, as for a type alias. A recursive type may not hold a class's type at itself (`kids~List (Display.Options Tree)` in `Tree`, E0354): what the instance gives isn't known while the type is checked, so it is taken as possibly negative.
- **`==`** (D125 b) treats `C.Name a` as it treats a type parameter. **Coherence** is unchanged: one instance per type constructor, so `Display.Options Money` has one meaning wherever `Money`'s instance is loaded.

**Constraints on a class's types (#176).** After `type Name`, or a default `type Name = T`, come the constraints a signature takes, about `Name`: class clauses, and predicates on a value of it.

```checkers
class Seq s
    type Elem : Ord Elem                       # its values have an order
    fn uncons xs -> r : xs~s, r~Option (Elem, s)

class Encoding s
    type Unit : u~Unit, code s u < 256         # every value's code is below 256
    fn code s u -> n : s~ghost Type, u~Unit, n~Nat
    fn units x -> us : x~s, us~List Unit
```

- **A clause** is a class of the type itself, `D Name` (E0370 otherwise). Each instance's type must have it: the dictionary is found at the instance's `type Name = T` (at its header for a default), as any clause is (E0284 if there is none, `help:` naming the context to add). In generic code with the clause `C a`, `C.Name a` has it: the dictionary is a field of `C a`'s, so `le x y`, `x <= y` and passing values to a function with the clause `D b` work. A clause on a class's type in a signature (`Add (Seq.Elem s)`) is an ordinary clause: an implicit parameter, found once `s` is known.
- **A predicate** names a value of the type first, `u~Unit` (E0370 if it doesn't, if the name's type isn't the type, or if a second name is given), and may use the class's functions. A class's type is a type of its own (above), so a predicate reaches its values through them: `u < 256` is E0210, whose `help:` says so. A function used there whose arguments don't tell the instance takes the class's parameter explicitly (`s~ghost Type`, #161), since `C.Name a` doesn't determine `a`.
- **Checked at each instance.** Every predicate holds of every value of the type the instance gives, or takes as the default: a proof by Z3, with the instance's functions. `type Unit = U8`, with `code` its value, proves `code s u < 256`; `type Unit = Nat` is E0450 at `type Unit = Nat`, "cannot prove that every `Nat` satisfies `code s u < 256`, as `Encoding.Unit` requires", with a counterexample (`u = 256`). A default is checked at each instance that takes it (reported at its header), since its predicates are about that instance's functions.
- **Assumed in generic code.** With the clause `C a` in scope, every value of `C.Name a` satisfies the predicates: the prover assumes them of each such value, a parameter, a local, a field, an element, a call's result, as it assumes a refinement alias's (§7.3). At a known instance, `C.Name t` is the instance's type, whose own refinement implies them.
- **At run time** a clause's dictionary is a field of the class's dictionary; predicates are erased.

**Classes of several types (#145).** A class may take several type parameters, `class Hole s h`, when what is allowed is a property of the types together: which hole types a formatter accepts.

```checkers
class Hole s h
    fn hole tag x -> r : tag~s, x~h, r~String

instance Hole Format a : Display a    # any type with a display
instance Hole Page String             # only strings
instance Hole Plain String
instance Hole Plain Int               # strings and ints, nothing else
```

- **Declaring.** Each function and lemma mentions every parameter of the class in its parameters' types, or takes it explicitly as `t~ghost Type` (above), as `class TryFrom s t` with `fn try_from x t -> r : x~s, t~ghost Type, r~Option t` does (E0368 otherwise, at the member, naming the parameter): otherwise a use couldn't tell which instance it means. Each parameter's kind comes from how the members use it, as for one parameter (M25).
- **An instance** gives a type for each parameter (E0292 otherwise). Each is a type constructor applied to distinct type variables (E0281), or a bare type variable, except the first, which can't be (E0281); the variables are distinct across all the types (E0281). Its context is classes of those variables. With one parameter, `instance Ord List a` is E0292 too (`instance Ord (List a)` is meant).
- **Coherence.** An instance is declared in the package of the class, or in the package of the type constructor of one of its types, provided no type before it is a bare variable (E0282, labelled at the variable when one comes first): Rust's orphan rule ([RFC 2451](https://rust-lang.github.io/rfcs/2451-re-rebalancing-coherence.html)). So `instance Hole Format Money` may be in `Money`'s package though `Hole` and `Format` are foreign there; `instance Rel Format a Money` may not, since the bare `a` comes first (it may be in `Format`'s). This is coherent across packages: of two overlapping instances in different packages, allowed by their types at positions i and j, i = j can't overlap (types of different packages at the same position); if i < j, the second has at position i the first's type (a bare variable there is forbidden), so its package depends on the first's and sees its instance, and the overlap is found there; j < i likewise. An instance in the class's package is seen by every package that can use the class. Two instances whose types can match the same types are E0283: at each position the same type constructor, or a variable in either (`Hole Format a` and `Hole Format String` overlap; `Hole Format a` and `Hole Page String` don't).
- **Using a class.** A clause `Hole s h` is an implicit parameter, the dictionary, as for one parameter. An instance is chosen once the use's types are known wherever the instance names a type constructor; where it has a bare variable, that type need not be known yet. With `instance Hole Format a : Display a`, a use at `Format` with the hole's type not yet known chooses it at once, and its `Display a` waits for `a`. With `instance Hole Page String`, the use waits until the hole's type is known, even though it is `Page`'s only instance; with `Hole Plain String` and `Hole Plain Int`, the same. An instance is never chosen because the others have been ruled out: instances are registered as their modules are checked, so the set visible at a use depends on what has been loaded, and choosing "the only one left" would give a use different meanings in different module orders. E0284 if no instance can match; E0285 if the types an instance needs never become known (its label names the instances that could match, when there are several). A dictionary in scope is used for exactly its types: a use whose unknown types it could match waits for them.
- **A class's types** are given by each instance; outside the class, `Hole.Options s h`, a type for each parameter (E0291 with fewer). In the prover, at a dictionary in scope, it is a sort of its own applied to the sorts of all the types.
- Everything else is as for one parameter: the dictionary is a record of the class's functions; a known instance's functions are visible to the prover and an unknown dictionary's fields are uninterpreted; a class's lemma is assumed for every dictionary; termination through dictionaries is found the same way. A class with one parameter is unchanged.

**Sequences (#169).** The prelude's class `Seq` lets the patterns `[]`, `x :: rest` and `[p1, …, pn]` take apart any type with an instance, as `Add` lets `+` work on any type with one: a function written once works on lists, arrays (`Bytes` too) and strings.

```checkers
export class Seq s
    type Elem
    fn size xs -> n : xs~s, n~Nat
    fn uncons xs -> r : xs~s, r~Option (Elem, s),
                        match r
                            None           -> size xs == 0
                            Some (_, rest) -> size rest < size xs

fn count xs -> n : Seq s, xs~s, n~Nat
    match xs
        []        -> 0
        _ :: rest -> 1 + count rest
```

- **Instances.** `List a` (`Elem` is `a`; `size` is the length), `Array a` (`Elem` is `a`, so a `Bytes`' is `U8`; `size` is `len`) and `String` (`Elem` is `Char`; `size` is the number of bytes, which `uncons` makes smaller by a whole character). All three are in the prelude, so a `match` needs no import.
- **Patterns.** On a value whose type is not `List` and has a `Seq` instance, or is a type parameter with a clause `Seq s` in scope, `[]` matches where `Seq.uncons xs` is `None`, `p :: q` where it is `Some (x, rest)` with `p` matching `x` and `q` matching `rest`, and `[p1, …, pn]` is `p1 :: … :: pn :: []`. A nested pattern takes `rest` apart with another `uncons`. `uncons` is called once for each value taken apart, however many arms test it. On `List a` a `match` is built in, unchanged (its constructors and these patterns mix, its proofs and memory reuse are as before), as numbers keep their built-in `+`; so is a `match` on a value whose type isn't known yet. A `let` or a lambda's parameter takes a sequence apart the same way.
- **Mixing** these patterns with the type's own constructors in one `match` (`String b` and `[]` on a string) is E0248. A type with no instance and no clause is E0241, as before.
- **Exhaustiveness** is that of a `match` on `Option`: `[]` and `_ :: _` cover everything. A missing case is shown as a pattern of the sequence (`[]`, `_ :: []`).
- **Termination (§5.3).** `uncons`'s postcondition is a fact after each of its calls, as for any call (D50), so in a `::` arm `Seq.size rest < Seq.size xs` is known; guessed measures try `Seq.size` of a parameter taken apart so. Each instance proves the postcondition in its `uncons`.
- **In the prover (§7.3)** the patterns are the `match` on `uncons`'s result they stand for.
- **At run time** `uncons` on an array takes constant time: the rest is a slice sharing the array's storage (§14). On a string it is written in Checkers from two builtins on a non-empty string, `string_first` (the first character, decoded) and `string_rest` (the rest of the bytes, a slice sharing them): `if len s.bytes == 0 then None else Some (string_first s, string_rest s)`.
- **Building values** is not part of this: `[]`, `x :: xs` and list literals build lists.

The prelude declares `Ord` (`le`; `trans`, `total`, `antisym`) and the lemma `refl`, with instances for `Int` (so `Nat`, `Char` and the fixed-width numbers), `Bool` (`False` first), `String` (by bytes, which is by scalar values; a builtin with three axioms), `List a` (lexicographic) and `Option a` (`None` first); `Functor`, with instances for `List` and `Option` (`std.array` has `Array`'s); and `Seq` (`Elem`, `size`, `uncons`), with instances for `List a`, `Array a` and `String`.

### 9.9 Named preconditions and `forall` (D137, M23)

`name: p` names a precondition. `forall x y : x~a, y~a, c1, …, cn` holds of all values of its variables: its clauses are the ones that follow and mention a variable (parenthesize to end it sooner), the last its conclusion. It may appear only in a named precondition or a lemma's `ensures` (E0289), in a positive place: the precondition itself, under `and` or `or`, after `implies`, inside another `forall`'s conclusion (E0289 otherwise).

- Its variables range over their types wherever the prover proves or uses it: a `Nat` is non-negative and a refinement's predicates hold.
- **At a call** it is an obligation, proved with fresh values for its variables, which are known to be in their types. A `forall` precondition of the calling function whose variables have the same representation (`Nat`, `Int` and refinements of `Int` share one) is given at those values where they are in its own variables' types, so a function passes its own hypothesis on: one over `Nat` meets one over a refinement of `Nat`, not the other way round.
- **In the body** it is not given to Z3. `have name a b …` fills in the variables of its `forall`s, left to right, and gives the rest as a fact (E0290 if the count doesn't match).
- A `forall` precondition guards nothing: a call's postconditions are assumed without it, since it is proved at that call.
- **A lemma's `ensures`** may be a `forall` (D146). Its `proof` has the variables in scope by name and the premises as facts. `have l a b` with the lemma's arguments brings the `forall` into scope, given at fresh values as a precondition is; `have l a b x y` also fills in its variables.

```checkers
lemma total_by key : Ord k, key~(a -> k)
    ensures forall x y : x~a, y~a, le (key x) (key y) or le (key y) (key x)
    proof
        have total (key x) (key y)
```

### 9.10 Templates (#132)

A string literal glued to a lower-case name before it is a **template**: `tag"text {e} text"`. The name is the *tag*, a function in scope: a qualified one (`app.page"…"`) and a partial application bound to a name (`let q = sql conn`, then `q"…"`) are tags too. A string not glued to a name is unchanged, as is one glued to a keyword (`then"a"`).

- Inside the quotes, text is as in a string, with its escapes; `{{` and `}}` are `{` and `}`. `{…}` is a **hole**; a `}` that closes none is E0005.
- A hole is `{e}`, the expression `e`; `{e | o1, o2}`, `e` with the options `o1`, `o2`; `{}`, a new parameter of the template; or `{| o1, o2}`, a new parameter with options. `e` and the options are expressions, checked in the template's scope, each with its span inside the literal.
- A hole ends at the `}` that closes it; it may hold brackets, strings and templates (`{f "a"}`). `|` splits it only outside brackets. A hole still open at the end of the line is E0006. A `:` in one is E0100 (it is no part of an expression), and so is a `#` (E0001: a comment would never let the hole close).
- The options are the inside of a list, as a direct call writes it: `{x | Precision 20, Padding 20}` passes `[Precision 20, Padding 20]`. `{x |}` is E0100.

**Formatters.** `std.string` declares the classes a template is built through, and `NoOptions`, an enum with no constructors. A template needs no import: `std.string` is loaded for a module that has one (its tag is a name like any other: `std.string`'s own, `format`, is imported, §9.11). A formatter's instances name the classes, so its module imports them, `import std.string (Template, Hole)`; their functions are names only where imported.

```checkers
export class Template s
    type Result
    fn text st str -> r : st~s, str~String, r~s
    fn finish st -> r : st~s, r~Result

export class Hole s h
    type Options = NoOptions
    fn hole st x os -> r : st~s, x~h, os~List Options, r~s
```

A tag is applied to the number of bytes of the template's text (its escapes read, `{{` one byte) and its number of holes, and gives the first state. A hole's options are `Hole.Options` of the state's type and the value's, so each value type a formatter takes may have options of its own.

**Meaning.** `tag"a{x}b{y | o}c"` is

```checkers
Template.finish (Template.text (Hole.hole (Template.text (Hole.hole (Template.text (tag 3 2) "a") x []) "b") y [o]) "c")
```

with `std.string`'s functions, whether or not the module imports them, and whatever its own names mean. Empty text pieces are left out. With positional holes it is a lambda taking them in order: `tag"{}, {}"` is `\a0 a1 -> Template.finish …`, so a positional hole's type comes from where the template is used, as a lambda parameter's does (`page"<li>{}</li>" name`).

- Each call is an ordinary use of a class (§9.8), at a span inside the template. `hole`'s instance is found at the hole's value (at the hole, for a positional one): a value of a type no instance takes is E0284 there ("no instance of `Hole` for `Page` and `Nat`"), and one whose type never becomes known is E0285 there. `text`'s and `finish`'s are found at the tag. An option of the wrong type, and an obligation inside a hole, are reported at the option or the expression.
- **The tag first.** The tag's first state, `tag n k`, is checked before anything else. If that fails (`tag` is unknown, or isn't a function of two numbers), or its type can't have a `Template` instance (it has none, or it is a type parameter without the clause `Template s`), that is the template's only error, at the tag (E0284 for a missing instance: "no instance of `Template` for `Int`: `count` isn't a template's tag"); the holes and options are not checked. A type not yet known waits, as for any use of a class.
- In the prover a template is its calls: what is known of the result comes from the instances' functions, as for any code.

### 9.11 Showing values (#126)

There is no built-in `format`: `std.string` shows values through two classes, and its `format` is a template's tag (§9.10) built on one of them. None of these is in the prelude; a module imports them, `import std.string (format, display, debug)`.

```checkers
export class Display a
    type Options = NoOptions
    fn display x os -> s : x~a, os~List Options, s~String

export class Debug a
    fn debug x -> s : x~a, s~String
```

**`Display`: for users, with options of the type's own.** `display x []` shows `x` without options. An instance chooses its options' type, or leaves it out for `NoOptions`. Options are typed, so an option a type doesn't take is a type error at the option, and every list of a type's options is accepted: where two conflict, the later one wins. No instance is derived: a type shows for users only as its author writes it, in the module that declares the type (§9.8's coherence). At a type parameter, `display` needs the clause `Display a` (E0284 without it); generic code can pass only `[]` or options it was given. There are no instances for containers (`List`, `Option`, `Result`, tuples, `Array`), not even conditional ones, and none for `Unit`. Padding is not an option: a program pads with ordinary functions.

| Type | Options | Shows |
|-|-|-|
| `Int` (so `Nat`, the fixed-width types and `Char`, which are refinements of it) | `IntOption`: `Hex`, `Binary`, `Octal` (after `0x`, `0b`, `0o`, lower case), `Plus` (a `+` before a non-negative number), `Digits n` (at least `n` digits, zeros before them and after the sign and prefix) | decimal; without options, `Parsable.parse` reads it back, and a number that isn't negative starts with a digit, and with `0` only when it is `0`, as the instance's own signature promises (§9.8) |
| `String` | `StringOption`: `Quoted` (as `debug` shows it), `Take n` (the first `n` scalar values, then quoted if asked) | the string itself |
| `Bool` | `NoOptions` | `True`, `False` |
| `Decimal` (`std.decimal`) | `DecimalOption`: `decimal.Plus`, `Places n` (rounded to `n` digits after the point, half away from zero, never with an exponent) | as `decimal.render` writes it |

The instances for `Int`, `String` and `Bool` are in `std.string`, beside the class; `Decimal`'s is in `std.decimal`. `std.decimal`'s `Plus` is written `decimal.Plus` where `std.string`'s is also in scope.

**`Debug`: Checkers source, for every type.** Every type has a derived instance that writes a value as source: `Some (Ok 1)`, `[1, 2]`, `(1, "a")`, `b"…"`. Strings are quoted at every level, the top included (`debug "a"` is `"a"` with the quotes); functions and capabilities are `<function>`, `<Term>` and so on, so a failed `check`, a counterexample and generic code can always show a value. `debug x` needs no clause at a type parameter.

- **By type (#170).** A value is shown as its type says, not only as it is stored, at every level: a type stored as its one field (§14) shows its constructor (`Meters 3`); a `String` and a `Bytes` are both bytes, and show as `"…"` and `b"…"`; an `Array U8` shows as `b"…"` and an `Array U32` as `[…]`. At run time `debug` is given its type's descriptor (§14), and so is every function that shows values of its type parameter, with `debug` or through a function it calls with that parameter: generic code shows values as code at a known type does. So does everywhere else a type comes from: a class's type kept in a dictionary (§9.8), a type constructor parameter applied (`f String`, M25), a field whose type is computed from earlier fields (`v~(if is_text then String else Int)`) or from a value its type is applied to (`ByParam True`), and a `Bag`'s elements.
- **A type not known when the program is compiled is an error (E0293).** Where such a function is given a type that depends on a value known only when the program runs, there is no descriptor to give: `` `show` shows values of type `a`, so `a` must be known when the program is compiled``. The label names the type and what it depends on: a variable (`if b then U8 else Int`, `ByParam b` where the field's type is computed from `b`), or a field whose type is computed from something not kept when the program runs (a ghost field). Through other functions, as for `==` (D125 b): `(through \`debug\`)`.
- **`String`** is shown by `std.string`'s `instance Debug String`, written in Checkers: in quotes, with `"`, `\`, newline (`\n`), carriage return (`\r`), tab (`\t`), NUL (`\0`) and the other control characters (`\u{…}`) escaped. Nothing else about strings is special to `debug`.
- A type's own module may write `instance Debug T` to replace the derived one, and so may the class's module, `std.string` (which is how the prelude's `String` has its own). Elsewhere it is E0282 (another package, §9.8's orphan rule) or E0283 (another module of `T`'s package: it overlaps the derived instance). It takes no context (E0281): `debug` needs no clause at a type parameter, so a context would add nothing. Its function is given the descriptors of `T`'s arguments, so it may show values of them with `debug`.
- It is found at run time through the value's type: wherever a `T` is shown, inside other values and through generic code. In argument position its text is put in parentheses if it has a space outside brackets and quotes, as a constructor's fields are.
- `Debug` takes no options, and templates treat it like any function: `format"{debug x}"`, or `format"{}" (debug x)`.
- The runtime's printer is the derived instance, and the text of a failed `check` (§13.3) and of a counterexample, at every level, whatever a type's own `Debug` says: two different values never look the same there. The standard library's own instances (`String`'s) are used there too. A failed `check` writes a `String` as a string literal, with the same escapes, as it writes a `Char` as `c'a'`: its module may not load `std.string`.

**`format`.** `std.string`'s template tag:

```checkers
export record Format
    parts~List String                 # the last first

export fn format n k -> f : n~Nat, k~Nat, f~Format
    Format []

instance Template Format
    type Result = String
    fn text f str
        Format (str :: f.parts)
    fn finish f
        concat (list.reverse f.parts)

instance Hole Format a : Display a
    type Options = Display.Options a
    fn hole f x os
        Format (display x os :: f.parts)
```

```checkers
format"{name} is {age}"               # Ada is 36
format"{n | Hex, Digits 4}"           # 0x00ff
format"{| Quoted}" name               # "Ada"
format"{debug point}"                 # Point 1 2
format"{point}"                       # error at `point`: no `Display` instance for `Point`
```

- It accepts any type with a display, through one instance over all of them; a hole's options are its value's type's own, and an error in a hole is at the hole (E0284 for a value with no `Display`, a type error at an option of another type).
- It is imported like any other `std.string` name: `import std.string (format)` for `format"…"`, or `import std.string` for `string.format"…"`. Without an import it is an unknown name (E0204). The compiler knows nothing special about it: an unknown name that a standard-library module exports gets a `help:` naming the import (`add \`import std.string (format)\``), whatever the name.
- `format x`, a call of a tag on a value, is an ordinary type error, as for any function of two numbers. Where a function whose result has a `Template` instance is called outside a template, a type error at the call or at its first argument gets a `help:` saying the function is a tag: ``write `format"…{x}…"` to put `x` in a template``.

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
| M19 | `checkers lsp` (D120, §15.5): diagnostics on every change (types first, then proofs), hover, go to definition, semantic highlighting, formatting, document symbols | the scripted sessions in `tests/lsp/` (requests in, expected responses out) pass; type errors reach the client in under 100 ms on `tools/checkers.ck` (measured); Ian confirms it works in Emacs with Eglot (done 11/15/2026: Ian confirmed it works in Eglot) |
| M20 | Checking past errors and `Nat` as a refinement of `Int` (D121, D122), `main` on a fiber (D123) | `Int` and `Nat` mix and convert as D121 says, with golden tests; proving time measured before and after; a file with a syntax error and a type error still gets the other declarations' type errors, proofs and `check`s (golden tests in `tests/types/`, `tests/json/`, `tests/lsp/`); a program reading standard input in a loop in `main` runs its behaviours on one thread (`tests/run/`) (done 11/11/2026: `tests/types/nat_int`; checking every example, the tool and `std` with no cache about 31 s before and after, the tool's 347 obligations unchanged; `tests/types/past_errors`, `tests/json/past_errors`, `tests/lsp/past_errors`; `tests/run/main_waits`) |
| M21 | Arrays (D133, §9.5): `Array a` in the prelude, `Bytes` as `Array U8`, `std.array`, packed layouts for every fixed width, layout arguments for generic code, the prover's `(Seq S)` | every existing test, example and tool gives the same output with `Bytes = Array U8`; `tests/run/` cases for each packed width (signed, unsigned, `U64` beyond 63 bits), for generic code creating arrays of `U8` (packed, printed as `b"…"`), for `set` in place and copied, and for an `Array U8` used as an `Array U32`; `tests/types/` for indexing and `==` on arrays; proofs about `std.array`'s postconditions; `examples/wc.ck` as fast as before | done (11/13/2026): `tests/run/arrays` (every width at its edges, `U64` and `I64` past 63 bits, `Bool`, `Char`, generic `map` to `U8` packed and printed as bytes, `set` on a shared array copying and on an unshared one in place, an `Array U8` used as an `Array U32` widened by `set`), `tests/types/arrays` (an `Int` element isn't a `U8`, with the counterexample `array.from_list [256]`; `==` on an array of functions, E0263; out of bounds), `std.array`'s own `check`s, layout unit tests in `rt/src/array.rs`. Indexing an `Array U8` stays inline without checking the object's kind (it is always bytes); `len` of a string, bytes or array is now inline too, so `examples/wc.ck` is about 3% faster than before |
| M22 | Function values in proofs (D139): function types as uninterpreted sorts with `apply`, defining equations for named functions, partial applications and lambdas | `std.string.concat_map_chars` proved instead of `__builtin`; a lemma about `list.map f` for any `f` proved; a call of an unknown function value's postcondition used in a proof (D84); `tests/types/` cases for each; proving time measured before and after (done 11/13/2026: `tests/types/fn_values` (a lemma about `map f` for any `f`, used at a parameter; `map` of a lambda using a local; a partial application of a parameter; an unknown function's postcondition through `map`; a function in a record; one that can't be proved); `concat_map_chars` proved from the axiom `concat_join` (D139 e); `tests/types/prove`'s example outside the fragment is now a function of a type; checking the examples and tools without the cache 17.3 s before and after) |
| M23 | Classes and sorting (D136–D138): `class`, `instance`, class clauses in signatures, class lemmas as obligations, coherence (orphan rule, no overlap), records of functions at run time; named `forall` hypotheses; `Ord` in the prelude; generic `Bag a` and `perm`; `sort`, `sort_as`, `sort_by` for `List` and `Array` | `list.sort` and `array.sort` proved sorted and permutations for any `Ord a`, and used at `Int` and `String`; `sort_by (\x y -> x >= y)` checks with nothing more written; an instance missing a lemma, a false instance lemma, an orphan and an overlapping instance each give a precise error (`tests/types/`); `examples/sort.ck` uses the generic sort (done 11/13/2026: `std.sort`'s `sort`, `sort_as`, `sort_by` and `std.array`'s proved, D138 g–i; `tests/run/sorting` sorts numbers, strings, booleans and a record with its own instance, by key and by comparison, lists and arrays; `tests/types/classes`, `class_errors`, `class_lemma_fails`, `forall`; `examples/sort.ck` sorts any `Ord a`; the tour's "Classes and sorting"; a program loading only the prelude proves its 44 obligations in about 0.2 s, `std.sort` in about 1.5 s) |
| M24 | Operators as class methods (D136 c, k): `+ - *`, negation and comparisons for types other than known numbers; algebraic classes with lemmas (`Semigroup`, `Monoid`) | a user type with `+` and `<=` through instances, its lemmas used in a proof; every existing test gives the same output (numbers unchanged); proving time unchanged (done 11/13/2026: the prelude's `Add`, `Sub`, `Mul`, `Neg`, `Monoid` and their `Int` instances, §9.8; `Semigroup` isn't separate: `Monoid`'s `assoc` is it; `tests/types/operators` (a vector type with `+`, `-`, negation and `Monoid`, a generic sum and a lemma using `add_zero`, comparisons of strings, lists and a record); every other test's output unchanged but the prelude's count in `checkers trust` (44 → 47 proofs, about 0.25 s)) |
| M25 | Classes over higher kinds (D136 c): parameters like `f~(Type -> Type)`, first-order unification of `f a`, variance; `Functor` with its identity and composition lemmas | `Functor` instances for `List`, `Option` and `Array`, their lemmas proved; a function generic over any `Functor` checks and runs (done 11/13/2026: §9.8, D136 (s)–(y); `tests/types/functor` (a program's own instances, for `Box` and for `Pair k`, one whose lemma fails, lemmas proved at any `Functor` and not without `have`, E0286, a type mismatch at `f a`, E0354 through a type constructor parameter), `tests/run/functor` (`doubled` at `List`, `Option`, `Array` and a record of the program's own); the prelude's count in `checkers trust` 47 → 53 proofs, its time unchanged (about 0.25 s), `std.list` 0.1 s more for `map_id` and `map_comp`; variance is the positivity rule (v), not marks on a type constructor's parameters) |
| M26 | Completion (D142): the cursor token, the parser's record of the place, the checker's of the scope; recovery in a body, after a trailing `.`, and of an unclosed bracket (D142 e); `ckc complete`; `completionProvider` with `.` as trigger character | the cases in `tests/proposed/complete/` give their lists; a completion request answers within 100 ms on `tools/checkers.ck`; the recovery cases keep the rest of the file checked (done 11/14/2026: `tests/complete/` (statements, arguments, members, types, conditions, declarations, proofs, patterns, imports), `tests/lsp/complete`, `tests/types/recovery`; measured: a completion request on `tools/checkers.ck` 60 ms (only the body the cursor is in is checked, and other modules' signatures; its types phase took 224 ms on the same 2-core machine, so D120 j's 100 ms no longer held for diagnostics there; after the profiling of 11/14/2026 (a refinement check that copied the context for every expression, arguments evaluated at every call for preconditions and measures most functions don't have, the context copied by every evaluation, and mimalloc for glibc's allocator, a third of the instructions) 125 ms, the whole check with Z3's answers cached 770 → 499 ms; of what is left, elaborating the standard library is about 45 ms, its lemmas' proofs about 20 of them)) |
| M27 | Literate documentation (D148, D151): `std.markdown` (CommonMark 0.31.2, ported from commonmark.js), `std.html`, the Unicode tables in `std.char` and `std.string`; links to symbols and compiled, run code blocks in doc comments, packages' `README.md`s and the site; their warnings (W030–W034) from `checkers doc`, `checkers site` and, for doc comments, `ckc check`; the language server in doc comments' code blocks | all 652 CommonMark examples pass; `std`'s documentation and the site build with no warnings; the site's and README's code checked through it (done 11/15/2026: `tests/run/commonmark`, 652 of 652; `tests/doc/literate`, `tests/types/doc_links`, `tests/json/doc_blocks`, `tests/complete/doc`; the golden tests build the site, the README and `std`'s documentation and require no warnings, D148 h–k) |


**Later** (noted, not scheduled):

- Regular expressions in `std`, working well at compile time too (staging, §8.9): a pattern known at compile time compiled then, as `fmt`'s format string is (Ian, 11/15/2026).
- User-defined resources (D156 a–c): a type declared as one (`resource record`, `resource enum`) follows D39's rules (used exactly once, never dropped by `_`, passed to generic code only as `own`) though it holds no runtime resource: a transaction to commit or roll back, a lock guard, a protocol's state that must reach its end (Ian, 11/15/2026).
- Borrowing a resource (D156 d, e, deferred: wants regions or lifetimes, not only borrows for one call): an operation that uses a resource without taking it (reading a `File`, a `TempDir`'s path), so the caller keeps it and the take-and-give-back pattern (`let (result, resource) = …`, D29) is unnecessary; only closing consumes it (Ian, 11/15/2026).
- Standard output and error as open files the program owns (Ian, 11/16/2026), not reached through `Term`: a program could close them (D156 k). Then writing to one from many behaviours, and to any file the program opened, by a copyable writer that only appends while the `File` stays with its owner. `std.terminal.stdin`/`stdout`/`stderr` give the stream's own `File`, not a handle of their own whose `close` leaves the stream open (§8.4, D112): closing it closes the stream, which is the point (Ian, 11/17/2026).
- ~~Remove `std.terminal.describe`: it only calls `files.describe` (Ian, 11/17/2026).~~ Done (11/17/2026): `examples/json.ck` and `wc.ck` call `files.describe`.
- ~~The site's header: a star counter for the repository at the top right, in place of the "Source" link (Ian, 11/17/2026).~~ Done (11/17/2026): a "★ Star" button at the right of the top bar links the repository; a script fills in the count from GitHub's API (`stargazers_count`, unauthenticated, kept an hour in `localStorage` since the API allows 60 requests an hour), and without it the button shows "Star" alone. On a docs page the version menu sits beside it.
- ~~Revisit `<-` and `let` (§8.4, D29): if one form can do what both do, keep `let` only (Ian, 11/17/2026).~~ Done (11/17/2026, D171): `let` only; `fork` and `join` are functions taking one-shot closures.
- Revisit `when` as a function of `std.cown` taking a one-shot closure, as `fork` and `join` became (D171 d) (Ian, 11/17/2026).
- ~~`let` with a refutable pattern wherever a one-branch `match` would do: `let x :: _ = l` where the facts in scope rule out the other cases (`l~List a, len l > 0`), proved as a `match`'s exhaustiveness is (D144) (Ian, 11/17/2026).~~ Already so: a `let`'s (and a lambda parameter's) pattern is a one-arm `match` (D144 e); found writing the Reference, with E0240 now naming the pattern (D167 i). Test: `tests/types/let_refutable`.

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

**Out of memory (D184).** Nothing is proved about memory, so a verified program can still run out of it. An allocation that cannot be made, whatever the size (more than the machine has, more than one allocation can be, or an array of a number of elements no machine word holds), ends the program with `checkers runtime: out of memory` and exit code 70. Nothing is written outside what was allocated. Where the operating system grants memory it does not have (Linux's overcommit), it may instead stop the program itself when that memory is used.

### 13.4 `main` and the root capability

`main` receives the command-line arguments after the file name, as `List String`, and the root `System` (§8.2). `term` reads standard input and writes standard output and error; `fs` is the process's file system with relative paths resolved against the current directory, and `files.within dir fs` confines it to `dir` (absolute paths and `..` are then refused). Operations on `env`, `proc`, `net` and `clock` are not implemented yet.

`IoError` values describe the operating-system error, as in `No such file or directory`. `read_line` (on `term` or a `File`) returns a line without its `\n`; bytes that are not valid UTF-8 become U+FFFD.

### 13.5 Behaviours (D44; M7: D66–D70)

`when`, `fork` and `join` schedule behaviours on a single FIFO queue that runs after `main` returns. The process exits when the queue is empty. If `main` returns a `Future ExitCode`, its value is the exit code.

**M7.** Behaviours run on a pool of worker threads:

- **Scheduling (D66).** Verona's algorithm (Cheeseman et al. 2023, §4): scheduling a behaviour appends it, in one atomic step, to the queue of every cown it names (a `fork` names a fresh future; a `join` names the futures it waits for). It runs when it is first in all of its queues, and on finishing it leaves them, which may make the next behaviours runnable. This gives causal order and freedom from deadlock by construction: nothing waits while holding a cown. Behaviours start as soon as they are runnable, while `main` is still running. The process exits when `main` has returned and no behaviour is queued or running.
- **Threads (D67).** `checkers run --threads N` (default: the number of cores) runs behaviours on N threads: N − 1 workers from the start, and the main thread too once `main` returns. `--threads 1` is the M2 scheduler exactly: one FIFO queue after `main` returns, so output is deterministic. An executable written by `checkers build` takes its thread count from the environment variable `CHECKERS_THREADS` (default: the number of cores). Golden run tests use `--threads 1`; stress tests (`tests/stress/`) run each program 10 times on 8 threads, compare its output lines sorted (D68 allows any order between behaviours that share no cown), and fail if any two runs differ.
- **Output (D68).** Each `terminal` call is atomic: lines from behaviours that share no cown may come in any order, but never interleave within a call.
- **`par` (D69).** The components of `par (e1, …, en)` run on threads of their own, at most N − 1 at a time across the program; when none is free, the remaining components run on the current thread. The result is the same tuple either way. A component on a thread of its own that joins a future not yet filled (§8.6) blocks that thread until a worker fills it (#57); a component on the current thread parks like any join. Such threads are not workers, so a worker is always left to run the `fork`.
- **Actors (D70).** `stdlib/actor.ck`: an `Actor s` is a cown holding state `s`, made by `actor.new init sched`; `actor.send a f sched` (with `f~(s -> s)`) schedules `when x = a using sched: f x`, so messages to one actor are handled one at a time, in the order sent. State invariants are refinement types on `s`, as for any cown (§8.5).

Cown invariants (§8.5) need no runtime support: inside `when l = log`, `l` has the cown's content type, so a refinement such as `len l <= 100` is a fact the prover uses (`examples/log.ck`).

### 13.6 Run tests

A run test is `tests/run/NAME.args`: its first line is the program to run (relative to `tests/run/`, so `../../examples/wc.ck` runs an example), and each further line is one argument. `cargo test` runs it with the `checkers` binary (`checkers run --threads 1`), the working directory `tests/run/`, standard input from `NAME.in` (empty if absent) and the environment variables `NAME.env` sets (a `VAR=value` on each line; `CHECKERS_RC_CHECK=1` shows how many objects a program keeps), and compares standard output, standard error and the exit code with `NAME.out`.

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
  │ `match`es on small functions' results resolved (inline.rs)
  │ closure conversion (lower.rs): every lambda becomes a function taking its closure and arguments
  │ recursion made tail recursion (tailrec.rs); results returned as their parts (unbox.rs)
  │ reference counting (rc.rs): dup, drop and reuse inserted (D74)
  ▼
first-order code ──codegen.rs──▶ Cranelift IR ──┬──▶ in memory (JIT): `checkers run`
                                                └──▶ object file + libcheckers_rt.a ──cc──▶ `checkers build`
```

**Parameters (D179).** The language has no limit on the parameters of a function or the fields of a constructor. A native function takes at most 64 parameters. Closure conversion curries a wider function: the function takes the first 64 parameters and returns a closure that takes the next ones, up to 64 at a time.

**Values (D73).** A value is one 64-bit word: `2n + 1` for an integer `n` that fits in 63 bits; `0` for an erased value; `8k + 2` for constructor `k` without fields; `8k + 4` for unit and the capabilities; otherwise a pointer to a heap object. An object is a header (reference count; kind, field count and constructor or arity) followed by its words. Closures hold a code pointer and their free variables; a partial application holds the function and the arguments so far. Bytes hold their bytes, and a string is stored as its bytes (#170). Numbers that don't fit, decimals, bags, files, cowns and futures are Rust values behind an object. Literals and the closures of definitions are static data that is never freed. Addition, subtraction, multiplication, division, remainder and comparisons of small integers, equality of small integers, byte indexing, and calls of closures of the right arity are inline; the rest calls the runtime. **Not yet:** leaving out the overflow check where a refinement bounds a number (`U8`); it changes no result.

**One-field types (#170).** A type with one constructor whose fields keep exactly one value at run time (ghost and implicit fields of multiplicity 0 don't count; a class's type kept in a dictionary does) is stored as that value, with no object around it: `record Meters` with `m~Int` is an integer, `String` is its bytes, a class's dictionary with one function is that function. Building one, reading its field and matching on it cost nothing. `==` and reference counting are unchanged, since such a value is equal to another exactly when their fields are; so is the prover (§7.3), which still sees a datatype (and, for `String`, its bytes). Every such type is stored so: nothing marks it.

**Arrays (D133).** An array object's header gives its length and how its elements are stored: one word each, or packed at 1, 2, 4 or 8 bytes, signed or not. Reading goes by the header. Code that creates an array from elements lays it out for its element type: every type argument is passed as its layout's word, in the argument slot it already had (until now `0`), so a generic function knows the layout of each of its type parameters and passes it on. `++`, `set` and slicing keep their arrays' layouts (D133 f).

**Slices (#169).** Slicing an array (`array.slice`, `array.take`, `array.drop`, `bytes.slice`, `uncons`'s rest) takes constant time: the slice is an object holding its length, a pointer to its first element and a reference to the array whose storage it shares (an array made any other way holds its elements after its length). A slice of a slice refers to the first array. So does a string's `uncons`, whose rest is a slice of its bytes. The shared array is freed with its last slice, so a short slice keeps a long array alive; `set` updates in place only an array that is not a slice and has no other reference. Reading an element, `len`, `==` and every builtin go through the pointer, so a slice and a copy behave the same; byte indexing stays inline.

**Type descriptors (#170).** A type argument's word is its layout (an integer whose low four bits are the layout's code) or, where values of the type are shown (§9.11), its *descriptor*: an integer tag `(n + 1) · 16 + layout` naming type `n` of the program, for a type without arguments, or a tuple of its arguments' descriptors followed by its tag. Tuple types have a tag of their own. The layout is read from either in the same way, so arrays don't care which they are given. A descriptor of a known type is static data; one built from a type parameter's (`List a` in generic code) is built where it is passed. Only the type parameters of functions that show values of them get descriptors (`debug`; every function that passes its own type parameter to one; an instance whose class's types, kept in its dictionary, are built from its own; each closed over each module's uses of generic functions and dictionaries, as for D125 b); every other type argument stays its layout, so code that shows nothing pays nothing. A class's type is kept in its dictionary as a descriptor. A type constructor parameter applied (`f a`) is described when the program runs, by adding `a`'s descriptor to `f`'s. A value argument of a type that its fields' types are computed from (`ByParam True`) is in its descriptor, marked as a value; it is known when the program is compiled (E0293 otherwise).

The runtime shows a value by its type's descriptor. Its constructors' field types, from the type's parameters, are in the program's descriptor, and so is how each type is shown (a list, an array, a bag, a type stored as its one field). A field whose type is computed from earlier fields or from the type's value arguments has a function computing its descriptor from them, compiled with the program; the runtime calls it when it shows the field. A `Bag` keeps one of each of its values, to show it by the element type. A failed `check`'s text and staging's reading back of computed values (§8.9) go by the type the compiler knows.

**Memory (D74).** Functions receive their arguments owned and consume them. Each variable a function binds goes to the last part of an expression that uses it; earlier parts borrow it, and a borrowed variable is duplicated only where it is kept (returned, stored, passed on). Primitives and builtins borrow their arguments, but for those that update an argument no one else refers to in place, which own theirs: `std.array.set`, the rest of an array or string in `Seq`'s `uncons`, which moves an unshared slice forward instead of making another (proposed), and `++`'s left side where `++` is its last use (see below). A comparison's result, `True` or `False`, is never counted. A `match` duplicates the fields its arm uses; if the arm doesn't use the value matched on, it is dropped, and if the arm builds a constructor with as many fields, the drop becomes a *reuse*: when it was the only reference, the new value is built in its memory. Counts are atomic. Constants (definitions without parameters) are computed on first use and kept for good. `CHECKERS_RC_CHECK=1` counts the objects left at exit (only constants' values should remain); `CHECKERS_NATIVE_DUMP=1` prints the first-order code with its reference counting.

**`++` in place (optimization).** Where `a ++ b` is the last use of the variable `a`, `++` takes `a` rather than borrowing it, and when that was the only reference to a string, bytes or array (not a slice, and not `b`) stored as `b` is (both bytes, or arrays of one layout), `b`'s elements are written after `a`'s in `a`'s own memory, grown if needed; otherwise the result is new and `a` is dropped. So `decimal (n / 10) ++ digit (n % 10)` builds its string without copying it at every step. It changes no result, failure or order of effects (a value no one else holds can't be seen to change); which `++`s it applies to is not part of the language, and a program must not rely on it.

**Calls (D75).** Every function uses Cranelift's `tail` convention; calls in tail position are `return_call` or `return_call_indirect`, so tail recursion runs in constant stack. Code runs on stacks of 256 MiB: every behaviour's fiber, `main`'s too (D123), reserved but only touched as used. The runtime calls compiled code through a generated trampoline, `ck_invoke`.

**Recursion made tail recursion (optimization).** Before reference counting, `src/native/tailrec.rs` rewrites a definition's function whose recursive calls leave a little work after them, so that it runs in constant stack. It changes no result, failure or order of effects; which functions it rewrites is not part of the language, and a program must not rely on it. Today, for calls of the function itself in tail position but for: a constructor around the call (`n :: f (n - 1)`; the cell is built first with the field empty, and a helper `f.dps` fills it and calls itself in tail position), with only variables or literals in the fields after the call; or `+` or `*` on the call and a variable or literal, or `++` with the call on its left (`f (n - 1) ++ s`), where a helper `f.acc` carries the operations so far as an extra argument. These operators are associative for every value (`Nat` and `Int` have no fixed size); a class's `+` is a call and is never rewritten. `CHECKERS_NATIVE_DUMP=1` shows the helpers.

**Results returned as their parts (optimization, proposed).** After `tailrec`, `src/native/unbox.rs` keeps constructor values that are built only to be taken apart from being built. What is known of every value an expression can give is its *layout*: built by one of some constructors, each with its fields' layouts, or a tuple of its components' layouts, or unknown. A value laid out as a constructor is a word naming the constructor (the word it would be without fields) followed by the words of its fields, laid out in turn; a type's constructors share the words after the first, and those a constructor doesn't use are `0`. So `Ok (v, rest)` and `Err e`, from one function, are three words: `Ok`, `v`, `rest` or `Err`, `e`, `0`. A tuple whose last component is a tuple keeps that component whole, since at run time `(a, (b, c))` is `(a, b, c)`. A layout is at most as many words as the `tail` convention returns in registers on the machine the code is compiled for (8 on x86-64, 6 on ARM64; never more than 8), nested as deep as fits; a wider result stays a value.
- *Functions.* When every path of a definition's function `f` ends in a constructor or tuple it builds (literals included), a failure, or a call in tail position of another such function, and some caller takes `f`'s result apart, `f`'s code moves to a function `f.parts` returning the words. Functions that call each other in tail position share one layout, so those calls stay tail calls. `f` itself calls `f.parts` and builds the value, for closures; a call whose value is needed whole calls `f.parts` and builds it in place; a tail call of `f` from another function stays a tail call of `f`.
- *Callers.* `let x = e`, where every value `e` can give is built in `e` or returned as words by a call, and the code after it only takes `x` apart (a `match` on it, a record's field, a tuple's components but the last, the last as the rest), binds the words to variables instead: `match x` chooses by the first, a field is its words. A field laid out in turn is taken apart the same way, or built where it is needed whole. This also covers a `match` on a small function's result that `inline.rs` couldn't resolve (its `let`s and branches in the way).
Each word is owned, as the field of a value no one else holds would be, so reference counting (below) treats them as variables; there is no value to drop or reuse. It applies wherever code is compiled (`ckc run`, `ckc build`, `check`s and staging). It changes no result, failure or order of effects: the words are computed in the order the fields were, and a value built anew can't be told from one never built. Building a value in place where a function used to return a literal one (a closure's call of `f` giving `Err "end"`) allocates where it didn't. Which functions and `let`s it rewrites is not part of the language, and a program must not rely on it. `CHECKERS_NATIVE_DUMP=1` shows `f.parts`, its result count, `multi(…)` for the words and `let v1 v2 v3 =` for their binding. After Baker-Finch, Glynn and Peyton Jones, *Constructed Product Result Analysis for Haskell* (JFP 2004), with sums and nesting as in GHC's worker/wrapper split.

**Classes' functions at known instances (optimization).** Where a class's function is called with a known instance's dictionary (`Seq.uncons xs` at `Array Int`, `le x y` at `List Int`), `src/native/ir.rs` compiles a direct call of that instance's function (`Seq (Array a).uncons`), with the arguments the instance's dictionary would give it: its types and its context's dictionaries (`Ord a` for `Ord (List a)`). The dictionary isn't built: building one computes nothing but the dictionary, and there is one instance per type (§9.8), so the call is the one reading the dictionary would make, as in the prover. It applies wherever code is compiled (`ckc run`, `ckc build`, `check`s and staging). It changes no result, failure or order of effects, and a runtime error names the instance's function as before; which calls it rewrites is not part of the language, and a program must not rely on it. `CHECKERS_NATIVE_DUMP=1` shows the direct calls.

**Specialization by dictionary (optimization; proposed).** Where a definition's function is called with a known instance's dictionary (built by an instance, maybe from other known instances through its context: `Ord (List Int)` from `Ord Int`), with no variables in it, `src/native/spec.rs` compiles the call as a call of a copy of the function in which that parameter is that dictionary, and so are the call's types and other erased arguments without variables. Inside the copy the class's functions are at a known instance, so they are direct calls (above), and its calls passing the dictionary on are specialized in turn: a generic parser over `Seq` and `Token` called on `Bytes` runs as code written for `Bytes`. It covers functions with clauses, instances' functions with their context's dictionaries, class functions with clauses of their own, classes with several parameters or over type constructors, and dictionaries passed through lambdas and partial applications in the copy. The copy keeps every parameter, and the call passes the same arguments in the same order (those put into the copy as nothing); building a dictionary computes nothing but the dictionary, so it changes no result, failure or order of effects, and a runtime error in a copy names the function it copies. There is one copy per function and arguments put in, so recursion and mutual recursion use the copy; code growth is bounded: an argument put in is at most 64 nodes, copies are made inside copies at most 16 deep, and a program has at most 4096 copies; past a bound the call reads the dictionary as before. A lambda applied directly (an instance's function as its dictionary holds it) is compiled as `let`s, a dictionary or variable substituted. It applies wherever code is compiled (`ckc run`, `ckc build`, `check`s and staging); which calls it specializes is not part of the language, and a program must not rely on it. `CHECKERS_NATIVE_DUMP=1` shows the copies under their function's name; `CHECKERS_NO_SPEC=1` turns it off, to measure it.

**Specialization by function (optimization; proposed).** The same copies are made for a call passing a *known function*: a lambda, a definition's function, or a definition's function applied to fewer arguments than it takes, each argument a variable, a literal, an erased argument, a known dictionary or a known function in turn (`digit`, `below n`, `\ys -> term self zs ys`). Computing one computes nothing but a closure. In the copy the parameter is that function, so calling it is a direct call (a lambda applied is compiled as `let`s), which returns its result as its parts (above) and can itself be specialized: `twice digit xs`, whose copy calls `digit` directly, or `fix`'s body and its `self`, whose copies call each other. The function's free variables (`n` in `\xs -> below n xs`) are passed to the copy as parameters of their own, after the arguments the copy is made for, so one copy serves every call passing the same function, whatever its variables hold, and a function passing its parameter on to itself (or the same lambda around it, as `fix` does) calls its own copy. A `let` or a lambda's parameter bound to a known function stays known: where it is called, the function is called directly, and where it is passed, the copy is made for the function. Any other use is the variable, so its closure is built once, and only if there is such a use. Likewise, a copy keeps a parameter it uses as a value. Calling it is not such a use, and neither is passing it to a parameter that is not used as a value in turn. The call then passes the closure as well, and the copy uses it there, so a function a loop keeps in a list is one closure, not one per iteration. Such a variable inside a function put into a copy is passed to the copy only if the copy uses it as a value; otherwise the copy gets the function it is bound to. Evaluating the arguments is unchanged, since a function's free variables are already computed, and so is every result, failure and effect; a runtime error in a lambda's body names the function the lambda is written in, wherever its code is copied. The bounds above apply: a function put in is at most 64 nodes, so one growing at each call (`\y -> f (f y)`) stops being specialized. It applies wherever code is compiled; which calls it specializes is not part of the language, and a program must not rely on it. `CHECKERS_NO_SPEC=1` turns it off too.

**A `match` on a small function's result (optimization).** Before closure conversion, `src/native/inline.rs` resolves a `match` on a call where it can, so that `match xs` with `[]` and `x :: rest` on an array builds neither the `Some` nor the tuple `uncons` returns. A `match` whose scrutinee calls, with all its arguments, a definition's function that is small (its erased body at most 40 nodes) and not recursive (no chain of calls from it leads back to it) gets that function's body instead, each argument bound by a `let` in order, so each is computed once, before the body, as for the call. A `match` on a `let`, an `if` or a `match` then moves past the `let`s and into the branches, but only where no arm of the outer `match` would end up in two places (no code is copied; otherwise only the `let`s are passed). A `match` on a constructor applied to its fields binds them in order and runs that constructor's arm, and a tuple used only through its components isn't built. Then a `let` whose value computes nothing that can fail or be seen (arithmetic but division and `Nat` subtraction, comparisons, constructors, fields, lambdas, and the builtins `Seq`'s instances use for `uncons`, whose callers establish their preconditions) is moved past the `let`s after it into the one branch of the `match` that uses it (proposed), and `let x = e in x` is `e`, so a call there is a tail call. It applies wherever code is compiled (`ckc run`, `ckc build`, `check`s and staging). It changes no result, failure or order of effects, and a runtime error in code taken from a function names that function, as the call did; which `match`es it resolves is not part of the language, and a program must not rely on it. `CHECKERS_NATIVE_DUMP=1` shows code taken from another definition as `at defN:`.

**Runtime.** `checkers_rt`: allocation and freeing (each thread keeps the memory of the small objects it frees, a list per size up to a header and 15 words, at most 4096 blocks each, and allocates from it before the system allocator; proposed), big integers (`rt/src/num.rs`), the `__builtin`s of `stdlib/` (`rt/src/builtins/`), `debug`'s derived instance (finding a type's own `debug` through its constructors' descriptor, §9.11) and `==`, I/O with atomic terminal calls (D68), behaviours and `par`, the scheduler, fibers, the poller and the blocking pool (§13.8), and runtime errors (``runtime error in `f`: …``, exit code 70). Native code describes its constructors and definitions to the runtime in a short text descriptor. `checkers build` links with `libcheckers_rt.a`: the one named by `CHECKERS_RT_LIB`, else the newest next to the `checkers` executable or in `deps/` beside it.

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

- **Indentation:** 4 spaces per block level. A continuation line lines up with the first item after the open bracket it is inside, or after the `:` of a signature; otherwise it keeps the indentation its author gave it relative to the line it continues, at least 4 (D99). A block a continuation line opens (§9.1) is indented 4 from that line.
- **Spaces:** one on each side of a binary operator, `->` and `=`, and after `,` and a signature's `:`. None around `~`, inside `( )` and `[ ]`, after a unary `-` or `\\`, or around a glued `.` or `[` (D22); one inside `{ }` (D99). Application is separated by single spaces.
- **Alignment:** the `->` of the arms of one `match` line up (an arm with a guard is left out, D99), as do the `:` of the constructors of one `enum` (a constructor without constraints is skipped), unless a blank line separates them. Trailing `#` comments on consecutive lines start in one column; a blank line or a line without a trailing comment ends the run. The column is the furthest of each line's code end plus the spaces its author put before the comment, at least two (D99): a run that is already aligned stays aligned, wherever its code moves, and formatting twice changes nothing.
- **Blank lines:** at most one in a row; none at the start or end of a block; the file ends with exactly one newline. Trailing whitespace is removed.
- **Kept as written:** comment text, literals, the order of declarations and imports.

`tests/fmt/` has examples: each `.ck` is formatter input and its `.out` the output of `checkers fmt -` on it. The golden tests also require every `.ck` file in `tools/`, `examples/`, `stdlib/` and `tests/{types,run,stage,stress}` to be formatted, and every `.ck` file in the repository to format to a fixed point with the same syntax tree (`tests/parse/` and `tests/check/` keep their unformatted inputs, which test the lexer and parser).

### 15.5 The language server (M19, D120)

`checkers lsp` speaks LSP 3.17 over standard input and output. It is part of the build tool (D95) and runs the compiler as a process (D97), so the editor's diagnostics are the compiler's.

| Request or notification | Behaviour |
|---|---|
| `initialize` | advertises full document sync, hover, go to definition, find references, formatting, formatting on a line break (D158), go to type definition, highlighting and rename (D160), document symbols, completion (`.` triggering it) and semantic tokens (full document); UTF-8 positions if the client offers them, else UTF-16 |
| `didOpen`, `didChange`, `didClose` | stores (or drops) the text; kills the document's check in progress, if any (not other documents', D127 e), and starts one of the document with every open document as an overlay |
| `didSave` | nothing: proofs already run on every change |
| `textDocument/publishDiagnostics` | sent after each phase of a check: types, then `check`s, then proofs; each time with all diagnostics so far, for every file the check reached |
| `textDocument/hover` | the type of the name under the cursor, or a function's signature with its conditions, and its description (D128), from the index |
| `textDocument/definition` | the definition of the name under the cursor, from the index |
| `textDocument/references` | the uses of the name under the cursor in every file of its package (`ckc index`, D161), and its definition if `includeDeclaration` |
| `textDocument/typeDefinition` | the declaration of the type of the name under the cursor: a local's, a constant's, a field's, a constructor's value's, a function's result's (D160) |
| `textDocument/documentHighlight` | the places of the name under the cursor in this file, its declaration first (D160) |
| `textDocument/prepareRename`, `textDocument/rename` | a name declared in the package renamed at each of its places in the package's files (D161), including import lists; the new name spelled as the old (capitalised or not), not a keyword, not already a name in any of those files; otherwise an error the editor shows (D160) |
| `textDocument/semanticTokens/full` | names classified by the index (function, lemma, constant, type, constructor, field, parameter, variable, module) and keywords, comments, strings and numbers |
| `textDocument/formatting` | `format` from `tools/ck/format.ck`; a syntax error gives no edits |
| `textDocument/onTypeFormatting` | after a line break (`"\n"`, its only trigger): the new line's indentation (D158), as an edit of its leading spaces; none when it's already right |
| `textDocument/documentSymbol` | the file's declarations, from the index |
| `textDocument/completion` | keywords and names that can stand at the cursor, from `ckc complete` (below), run beside the document's check; each item replaces the word the cursor is in, in the compiler's order (`sortText`); `.` is a trigger character |
| `shutdown`, `exit` | ends the server, killing any check |

**From the compiler** (`ckc check --json`):

- One JSON object per line. Positions are `[line, column]` from 0, the column in bytes; paths are as the compiler opened them.
- `{"kind":"diagnostic","phase":P,"path":…,"start":…,"end":…,"severity":"error"|"warning","code":…,"message":…,"label":…,"notes":[…],"help":…}`, where `P` is `"types"`, `"checks"` or `"proofs"`; `label` and `help` may be `null`.
- `{"kind":"name","path":…,"start":…,"end":…,"class":…,"def":{"path":…,"start":…,"end":…} or null,"type_def":… or null,"renamable":…,"hover":…,"doc":… or null}`, where `doc` is the description of what the name refers to (the comment lines directly above its declaration, D128), for each name in the file being checked (the editor's document; its imports' names are found through their declarations, `def`).
- `{"kind":"token","path":…,"start":…,"end":…,"class":"keyword"|"comment"|"string"|"number"}`.
- The `name` and `token` lines come right after the types phase's `done` line (so its diagnostics don't wait for them), and are ended by `{"kind":"done","phase":"index"}` (D127 d), before the `check`s' diagnostics.
- `{"kind":"done","phase":P}` after each phase, always all four (`types`, `index`, `checks`, `proofs`). Errors don't stop the later phases (D122): they set aside only the `check`s and obligations that touch a declaration with errors.
- `--overlay FILE`: `FILE` holds a JSON object from paths to text; a path in it is read from there instead of from disk. `--overlay -` reads the object from standard input (how the server passes it).

The server keeps one cown for its output, so a reply and diagnostics published by a check never interleave, and one for what the checks share (the latest check, the diagnostics showing, the index); a check reads the compiler's output in a behaviour of its own, one phase per behaviour. Its loop runs in `main`, itself a behaviour (D123). Requests about a document are answered from the index of that document's latest check, waiting for it if it hasn't come yet (D127 c). Until a check's proofs are known, the previous check's proof diagnostics stay (so they don't flicker while typing); a check that ends without finishing a phase, unless a newer one killed it, is reported with `window/showMessage`, as is a compiler that can't be started. Tests in `tests/lsp/` are scripted sessions: a file of messages to the server and the messages expected back.

**Completion** (`ckc complete [--overlay MAP] FILE LINE COL`, D142; LINE and COL from 0, the column in bytes). The lexer puts a cursor token at the position: it replaces the word the cursor is in or at the end of, else it is inserted; in a comment or a literal there is no completion. The parser takes it as a name and notes the first kind of place it meets it in; the checker, where it elaborates it, notes the locals in scope, the type expected, after `x.` what `x` is, and in a `match` arm's pattern the type matched. Output: `{"kind":"complete","path":…,"start":…,"end":…}` (what is replaced), then `{"kind":"candidate","label":…,"class":…,"detail":… or null,"doc":… or null}` for each candidate in order, then `{"kind":"done","phase":"complete"}` (alone when completion doesn't apply). `class` is as the index's, or `keyword`, `class` (a class), `type parameter`. Order: locals (nearest first), keywords, the module's own names, then those from the prelude and imports; within each but the locals, those whose type (a function's result) is the type expected come first, then by name.

The keywords at each kind of place, from the grammar (§9.2):

| Place | Keywords | Names |
|---|---|---|
| A declaration | `export`, `fn`, `partial`, `enum`, `record`, `type`, `lemma`, `let`, `class`, `instance`, `check`; before the first, `import` | none |
| After `export` | `abstract`, `transparent`, `partial`, `fn`, `enum`, `record`, `type`, `lemma`, `let`, `class` | none |
| A statement | `let`, `have`, `if`, `match`, and `when`, `try`, `par` (outside a proof) or `auto`, `admit` (in one); the first of a function body or a proof, `decreasing` | locals but type parameters, values, modules; lemmas in a proof |
| Any other expression | `if`, `match`, and `try`, `par` or `have`, `auto`, `admit` | as a statement |
| After `have` | none | lemmas, classes, locals, modules |
| A signature's clause, `ensures` | `forall`, `if`, `match` | locals (type parameters too), values, classes, modules |
| A type, after `~` | `ghost`, `own`, `comptime` (a record's field: `ghost`); further in, none | type parameters, types, `Type`, modules |
| After `x.` | none | `x` a record: its fields; a module: its exports; a class: its functions and lemmas |
| A `match` arm's pattern | none | the matched type's constructors (else every constructor in scope) |
| After `import` (and `a.`) | none | modules: the standard library's, and the program's files and directories |
| A lemma's body, before `ensures` | `let`, `ensures` | none |
| After a lemma's `ensures` line | `proof` | none |
| After a multi-line `if`'s branch | `else` | none |
| A class's or instance's body | `fn`, `lemma`, `type` | none |

### 15.6 Documentation and the site (D131)

**From the compiler** (`ckc doc FILE`), one JSON object per line, from the syntax tree:

- `{"kind":"module","name":…,"doc":…}`: the module's name and description, the comment that opens the file (a first line `NAME.ck — Text` gives `Text`).
- `{"kind":"import","module":…,"as":…,"names":[…]}` for each import: the module, the name it is used by (`as`'s, else its last part), and the names it brings in unqualified.
- `{"kind":"decl","what":…,"name":…,"line":…,"signature":…,"doc":…,"items":[…]}` for each exported declaration, in source order. `what` is `fn`, `lemma`, `type`, `enum`, `record` or `let`; `signature` is the declaration as written up to its body (a lemma's up to `proof`; a long constant's value is left out); `doc` is its description (D128), or `null`; `items` are an enum's constructors or a record's fields (`{"name":…,"signature":…,"doc":…}`), none for an abstract type.

**`checkers doc DIR -o OUT [--name NAME] [--root PATH] [--label TEXT]`** documents the package in `DIR`: every `.ck` file under it, named by its `module` line. `NAME` defaults to the `name` in `DIR/checkers.json`, else to the directory's name, and must be a package name (lower-case letters, digits and `_`, starting with a letter; D177). If `DIR/checkers.json` declares dependencies, they are resolved as `checkers check` resolves them in `DIR` (§16.4; `DIR/checkers.lock` is updated), and the code blocks in its pages may import them; `PATH` is the way from its pages to the site's root, for the site's links (default `../..`); `TEXT` names the version, shown on each page. It writes, as `.md` and `.html`:

| Page | Navigation, on the left | Content |
|---|---|---|
| `OUT/NAME/index` | its modules | `DIR/README.md` if there is one (without its first heading), then the modules, each with the first sentence of its description |
| `OUT/NAME/MODULE` | `NAME.MODULE`, whose `NAME` leads back to the package's page; then each declaration | the module's description (the comment that opens the file), then each exported declaration: its signature as a code block, its description. A record's or an enum's code block lists its fields or constructors, each with its description as a comment above it. |

`MODULE` is the module's name without the package's (`std.list` is `OUT/std/list`). The Markdown twins have the same content, without the navigation.

**Links in signatures.** Each type or constructor named in a signature links to its declaration, if the package declares and exports it. Names resolve as in the compiler: a qualified name (`files.File`) through the import it names; otherwise the module's own declarations, then the names its imports bring in, then the prelude. After `~` and until the next top-level `,`, a name is a type; elsewhere a constructor if there is one, else a type (D26). Type variables aren't links.

**`checkers site SRC -o OUT`** renders each Markdown page `SRC/PAGE.md` (in subdirectories too: `SRC/reference/types.md`) to `OUT/PAGE.md` and `OUT/PAGE.html`, and writes `OUT/llms.txt`: the site's title and summary (from `SRC/index.md`), then a link to each page and to every Markdown page under `OUT/docs/latest/`.

**HTML.** Pages are written in Markdown (CommonMark, `std.markdown`, with GitHub's tables) and rendered by `tools/ck/literate.ck` (D148): `[name]` links lead to symbols' documentation, and Checkers code blocks are compiled, and run if they have `main`, their output shown after them. Code blocks marked `checkers` are highlighted (keywords, comments, strings, numbers). Each page's head names its Markdown twin, `<link rel="alternate" type="text/markdown" href="PAGE.md">`, and the site's `llms.txt`, `<link rel="describedby" href="…/llms.txt">` (as [llmstxt.org](https://llmstxt.org/) proposes); the page shows no link to either. The top bar links the site's home, the tour, the Reference (`/reference/`, D166), the packages' documentation ("Packages", always `/docs/latest/std/`) and, at the right, a star counter linking the repository (filled in from GitHub's API by a script); on a documentation page it ends with the version shown (`--label`) as a menu of the others, read from `/docs/versions.json` (`{"latest": "vX.Y.Z" or null, "versions": ["dev", "vX.Y.Z", …]}`, written by the Pages workflow). Choosing a version opens the same page in it, or that version's package page if the page doesn't exist there. Links within documentation stay within its version.

**Hosting.** GitHub Pages, from `.github/workflows/pages.yml`. It builds nothing: the site and `dev` come from the latest commit that passed CI on `main` (when CI passes, that run's commit), built with the `ckc` and `checkers` that CI run uploaded; each release's documentation comes from its archive. Publishing a release (or running it by hand) redeploys the same way, which adds the new release's documentation and leaves `dev` as it was. The documentation has one directory per version:

| Path | What |
|---|---|
| `/docs/dev/std/` | `main`, labelled `dev` |
| `/docs/vX.Y.Z/std/` | each release, as published |
| `/docs/latest/std/` | a copy of the highest release that isn't a pre-release (`v1.2.0-rc.1` is one); of `dev` while there is none |

`packages.md` links all of them, and `versions.json` lists them for the version menu; `llms.txt` lists `latest` only. A release's directory comes from the archive `checkers-vX.Y.Z-docs.tar.gz`, which the release workflow builds with the tag's own tools (`--root ../../.. --label vX.Y.Z`; it refuses a tag whose commit hasn't passed CI on `main`) and attaches to the (immutable) release, so a release's documentation never changes once published. The release workflow then starts the Pages workflow itself, since a release published by a workflow starts no other workflow.

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
| `std.prelude` | prelude + builtin | `Type`, `Nat`, `Int`, `String` (a record of its bytes, #170), `valid_utf8` (whether bytes are UTF-8, a builtin), `Array`, `Bytes`, `Bool`, `Unit`, `Option`, `Result`, `List`, `U8`…`U64`, `I8`…`I64`, `Char`, `not`; the class `Ord` (`le`, `trans`, `total`, `antisym`), `refl`, instances for `Int`, `Bool`, `String` (by `string_le`, D138), `List`, `Option`; the classes `Add`, `Sub`, `Mul`, `Neg`, `Monoid` (`zero`, `assoc`, `zero_add`, `add_zero`) with instances for `Int` (M24); the class `Functor` (`fmap`, `fmap_id`, `fmap_comp`) with instances for `List`, `Option` (M25); the class `Seq` (`Elem`, `size`, `uncons`) with instances for `List`, `Array`, `String`, which sequence patterns use (§9.8); not exported: `string_le`, `string_first` and `string_rest` (a non-empty string's first character, and the rest as a slice of its bytes, in constant time, builtins) and `array_rest` (an array but its first element, a slice) for `Seq`'s instances | exists |
| `std.list` | Checkers | `length`, `map`, `all` (both call their function only with elements of the list, §5.3; both `transparent`), `reverse`, `join`, `keys`, `contains`, `unique`, `count`, `max_of`, `take`, `drop` (past the end, `take` gives all of `xs` and `drop` gives `[]`, in their postconditions, #107), `head`, `sorted`, `sorted_as`, `sorted_by`, `perm` (any element type, D138), `sort`, `sort_as`, `sort_by` (stable merge sorts, proved sorted, permutations, of the same length; D138, D147), lemmas (among them `perm_middle`, `map_id`, `map_comp`) (among them `keys_append`, `contains_append`, `contains_reverse`, `unique_split`, D119); lengths: `length_append` (`length (xs ++ ys) == length xs + length ys`), `length_reverse`, `length_map`, `length_keys` (#107; lemmas rather than postconditions of `reverse`, `map`, `keys`, which cost every query that mentions them, **(proposed)**) | exists; planned: `filter`, `fold`, `find`, `any`, `zip`, `concat`, `index_of` with lemmas |
| `std.option`, `std.result` | Checkers | `map`, `and_then`, `or_else`, `with_default`, `is_some` / `is_ok` | planned |
| `std.bag` | builtin | `Bag a`, `of`, `count`, `sum` (multisets of any element type, for permutation proofs, D47, D138) | exists |
| `std.map`, `std.set` | Checkers | `Map k +v`, `Set k`: `empty`, `insert`, `remove`, `lookup`, `member`, `size`, `to_list` and their lemmas (`lookup_insert`, …), ordered keys (D15) | planned (§9.5) |
| `std.array` | builtin + Checkers | `from_list`, `to_list`, `repeat`, `init`, `map`, `set`, `slice`, `concat`, `reverse`, `all`, `contains`, `count`, `take`, `drop` (D133); `sort`, `sort_as`, `sort_by` (D138), the axioms `to_list_from_list`, `from_list_to_list`, `to_list_map`, and `slice_at`, `slice_append`, `concat_nil`, `concat_cons` (what `slice` and `concat` give, #69; `concat_nil xs` says `xs ++ concat [] == xs`, since `concat []` alone doesn't fix the element type); the lemmas `ext` (equal lengths and elements make equal arrays) and `slice_join` (`slice xs i j ++ slice xs j k == slice xs i k`), proved (#75); the axiom `uncons_slice` (`x :: rest` on an array: its first element and the slice after it, §9.8); `instance Functor Array` (M25) | exists (M21) |
| `std.bytes` | builtin + Checkers | `matches_at`, `slice`, `concat`; the axioms `slice_at`, `slice_append`, `concat_nil`, `concat_cons` (what `slice` and `concat` give, #69); the lemmas `ext` and `slice_join`, proved (#75) | exists |
| `std.string` | builtin + Checkers | `bytes`, `from_utf8`, `from_char`, `from_chars`, `chars`, `concat`, `concat_map` (Checkers, D139), `fold_case` (Unicode's full case folding, a generated table, D151), axioms relating them (D119; `concat_join` in place of the axiom `concat_map_chars`, now proved, M22); the classes `Template` (`Result`, `text`, `finish`) and `Hole` (`Options`, `hole`), and `NoOptions`, which templates are built through (§9.10); the classes `Display` (`Options`, `display`) and `Debug` (`debug`, the runtime's printer), `IntOption`, `StringOption`, instances of `Display` for `Int`, `String`, `Bool`, and the template tag `format` with `Format` (§9.11); `NumberError` (`NotFound`) and an instance of `Parsable` from `Int` tokens (`std.parse`): a whole number in decimal, with `-` before a negative one, as many digits as there are (`-0` is `0`, and leading zeros are allowed); `instance Display Int` promises in its own signature that `Parsable.parse` reads `display n []` back, and that a number that isn't negative is written starting with a digit, and with `0` only when it is `0` (#233, proposed); the lemma `parse_display` says it is read back with anything after it that doesn't start with a digit; the lemma `parse_digits b` says bytes `b` that start with a digit are read: the result is `Ok (n, rest)` with `n` not negative, `rest` shorter than `b` and the bytes of `b` from `len b - len rest` on, and `rest` empty or not starting with a digit (#264); not exported: `digits` (a number's digits in a base, in Checkers: at least one, and in base 10, proved to be digits with no leading zero whose value is the number) | exists; planned: `join`, `split`, `starts_with`, `ends_with`, `trim` |
| `std.char` | Checkers | `code`, `from_scalar`, `from_ascii`, `from_surrogates` (D119); `is_digit` (`0` to `9`, a character or a byte); `is_punctuation` (general category P or S), `is_space_separator` (Zs), from generated tables (D151) | exists |
| `std.utf8` | builtin + Checkers | `decode_at` (`Option (Char, (stop~Nat, k < stop, stop <= len src))`: a character and where its encoding ends, #44), `encode`, `encode_append`, `decode_from_char` | exists |
| `std.decimal` | builtin + Checkers | `Decimal`, `of_int`, `scaled` (`m × 10^e`), `mantissa` and `exponent` (the `m` and `e` of a number's form `m × 10^e` whose `m` has no zero as its last digit; zero's are `0` and `0`), the axioms `scaled_parts` (`scaled (mantissa d) (exponent d) == d`) and `scaled_ten` (`scaled (m * 10) e == scaled m (e + 1)`) (#233, proposed); `render` (Checkers, from `display` of whole numbers: `mantissa`'s digits with zeros after them for an exponent from 0 to 21, with a point among or before them for a negative exponent leaving at most 6 zeros after the point, otherwise with `e` and the exponent), `DecimalOption` and an instance of `Display` (§9.11); `DecimalError` (`NotFound`) and an instance of `Parsable` from `Int` tokens (`std.parse`), so from characters or bytes: a number as JSON writes it, the longest such prefix (`1.x` reads `1`, `012` reads `0`), its whole-number parts read with `Parsable Int Int`; the lemmas `render_starts` (`-` or a digit first) and `parse_render` (reading what `render` writes, followed by anything that isn't a digit, `.`, `e` or `E`, gives the number and what followed), proved; not exported: `fixed` (a number with a given count of places) | exists |
| `std.parse` | Checkers | the class `Parsable a t` (`Error`, `parse`): a value of type `a` read from the front of any sequence (`Seq`) of tokens of type `t`, with what is left of it, a suffix and shorter; both types are named at each use (`parse xs Decimal Int`), so one type can be read from several kinds of tokens; a type that may read nothing reports it as an error; the class `Token x t` (`token`, an element read as a token), with an instance for `Int`, so characters and bytes (`Char` and `U8` are `Int`s): `String`, `List Char`, `Bytes`, `List U8`; `suffix` (`rest` is what is left of `xs` after taking elements off its front) and its lemmas `suffix_refl`, `suffix_trans`, `suffix_size`; `consumed r xs` (a success left a shorter suffix: `parse`'s postcondition) and `within r xs` (a suffix, maybe all); combinators, each taking parsers as functions whose types say how much input each is given (no more than the combinator's, or less): `satisfy`, `at_end`, `map`, `both`, `or_else`, `optional`, `many`, `many1`, `sep_by1`, `chain_left`, `complete`, and `fix` (a rule that refers to itself: its body gets the rule as `self`, callable only on less input, so recursive grammars terminate without a proof of their own), with the lemma `fix_unfold` (`fix body xs` is `body xs (\ys -> fix body ys)`: what a proof about a rule made with `fix` unfolds it by, #231) | exists |
| `std.html` | Checkers | `escape`, `entity` (HTML5's named character references, a generated table, D151) | exists (M27) |
| `std.markdown` | Checkers | `Document`, `Block`, `Inline`, `Item`, `Span`, `Target`, `Definition`, `Reference`, `Level` (a heading's level, `1 <= n <= 6`: `Heading` takes only these, #164), `parse`, `parse_with`, `to_html`, `to_html_with`, `label_key`, `language`, `plain` (CommonMark 0.31.2, a port of commonmark.js, D148, D151); the parser has no fuel: each loop's measure is a position that moves on, proved (a link reference definition, an open tag's attributes, a domain's labels, a line's container blocks), or, for emphasis, the tokens and delimiter characters left (#164) | exists (M27) |
| `std.json` | Checkers | `Json`, `Error`, `ErrorKind`, `parse`, `render`, `depth`, `MAX_DEPTH`, the round-trip lemma `roundtrip`; parsing in two stages, each a parser in `std.parse`'s sense: `tokenize` reads bytes into `Tokens` (`End`; `Stop at pos kind`, bytes that aren't a token or nest deeper than `MAX_DEPTH`, with where they start and where and why reading them failed; `More t rest`, with an instance of `Seq`), each a `Located` (`at`, its first byte's offset, and `kind`, a `JsonToken`: `BeginArray`, `EndArray`, `BeginObject`, `EndObject`, `NameSeparator`, `ValueSeparator`, `StringToken s`, `NumberToken n` read by `Parsable Decimal Int`, `TrueToken`, `FalseToken`, `NullToken`), and `inside ts n` (its positions are in an input of `n` bytes); `instance Parsable Json JsonToken` (built with `fix`; its `Error` is `TokenError`: `left`, the tokens left where it happened, and `TokenErrorKind`: `UnexpectedToken`, `MissingValue`, `MissingKey`, `MissingSeparator`, `RepeatedKey k`), with `Token` instances for `JsonToken` and `Located`; `parse` reports the first error left to right, as one pass would: a builder error where the tokens stop at bytes that aren't a token is the error reading those bytes as what was wanted there gives; the round trip is the two stages' round trips composed (`render`'s bytes are read as its tokens, and the tokens as the value) | exists (M13; proven without `admit`s, M18) |
| `std.path` | Checkers | `join`, `parent`, `name`, `extension` (paths as `String`, `/`-separated) | planned (the tools compute these by hand today) |
| `std.system` | — | `System`, `ExitCode`, the authority types | exists |
| `std.terminal` | builtin | `Term`, `print_line`, `eprint_line`, `write`, `write_bytes`, `read_line`, `read_all`, `stdin`, `stdout`, `stderr` | exists |
| `std.files` | builtin | `Fs`, `File`, `IoError`, `Entry`, `read`, `write`, `list`, `create_dirs`, `open`, `create`, `close`, `read_line`, `write_line`, `read_some`, `read_exactly`, `read_rest`, `write_bytes`, `flush`, `within`, `describe` | exists |
| `std.env`, `std.proc` | builtin + Checkers | `get`, `executable`; `exec`, `run`, `spawn`, `wait`, `killer`, `kill`, `Child`, `Killer`, `Output`, `Stream`, `Streams`, `Spawned`, `pipe_end` | exist |
| `std.cown`, `std.future`, `std.actor` | builtin + Checkers | `Cown`, `new`; `Future`, `Types`, `futures`, `values`, `ready`, `fork`, `join`; `Actor`, `new`, `send` | exist |

Not in the standard library: formats other than JSON, Markdown and HTML's escaping, networking (`Net` waits for a program that needs it), command-line parsing, and anything else a package can provide.

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

A version, here and in the lock file, is three whole numbers in decimal, each `0` or without leading zeros (`1.01.0` is an error), as [Semantic Versioning §2](https://semver.org/#spec-item-2) requires. An unknown field, a missing required one, or a malformed value is an error with its line and column in `checkers.json`. The lock file (D111):

```json
{
  "json_schema": { "git": "https://github.com/example/json_schema", "version": "1.4.0", "commit": "3f2a9c…" },
  "shared": { "path": "../shared" }
}
```

Minimal version selection: if this package needs `json_schema ≥ 1.2.0` and another dependency needs `≥ 1.4.0`, the build uses 1.4.0, even if 1.9.0 exists ("the highest required versions … are the minimum versions that satisfy all requirements", [Go modules reference](https://go.dev/ref/mod)). Lean's Lake records git dependencies the same way, with a revision per dependency in `lake-manifest.json` ([Lake reference](https://lean-lang.org/doc/reference/4.34.0/Build-Tools-and-Distribution/Lake/)).

`checkers build` in a package: read `checkers.json`, resolve and fetch the dependencies, write `checkers.lock`, then run `ckc build --package json_schema=~/.cache/checkers/packages/json_schema/3f2a9c… --package shared=../shared --uses .=json_schema,shared … main.ck` (D111).

Inside `json_schema`, its own modules are `validate`, `schema`, …; to this package they are `json_schema.validate`, `json_schema.schema`, and it can import only what its own manifest names (D111).
