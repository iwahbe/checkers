# Notation

## Grammar

Syntax is given in a form of EBNF:

| Notation | Meaning |
|---|---|
| `'fn'` | the literal text `fn` (a keyword or a symbol) |
| `name` | another rule of the grammar, or a kind of token from [Lexical structure](lexical.md) |
| `a b` | `a` followed by `b` |
| `a \| b` | `a` or `b` |
| `[ a ]` | `a`, optionally |
| `{ a }` | `a`, zero or more times |
| `( a )` | grouping |
| `NL`, `INDENT`, `DEDENT` | the end of a logical line, and the start and end of an indented block ([Layout](lexical.md#layout)) |

For example, an import is

```text
import ::= 'import' qname [ '(' name { ',' name } ')' ] [ 'as' lname ]
```

that is, `import`, a dotted module name, optionally a parenthesized list of names, and optionally `as` and a name.

## Examples

Examples are complete modules. Where one is meant to fail, its block is marked `compile_fail` with the error code it fails with, and the site's build checks that it does fail with that error. The compiler's report is shown after such a block.

```checkers,compile_fail,E0204
fn twice x -> y : x~Int, y~Int
    x + z
```

## Terms

- A **constraint** is one item of a comma-separated list after `:` in a signature: a typing such as `x~Int`, or a predicate such as `x > 0` ([Types and constraints](types.md)).
- An **obligation** is a fact the compiler must prove for a program to be accepted, such as an index being in bounds ([Proofs](proofs.md)).
- The **facts in scope** at a point are what the prover may assume there: preconditions, the conditions of enclosing `if`s, and so on ([Proofs](proofs.md#facts-in-scope)).
- **Run time** is when the compiled program runs; **compile time** is when `ckc` checks it, which includes running `check` declarations and [staging](staging.md).
- A **specification** is code the program never runs: a refinement, a precondition or postcondition, an invariant, a lemma's statement or proof. It is checked and proved, then erased ([Running programs](execution.md#erasure)).
