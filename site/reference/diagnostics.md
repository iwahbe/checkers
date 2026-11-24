# Diagnostics

Every error and warning the compiler reports has a code. Errors stop a program from being run or built; warnings don't (`--deny-warnings` makes them errors). A diagnostic points at the code it is about, and most say what to do in a `help:` line.

Codes are never reused: a code whose rule is withdrawn is retired, not given a new meaning.

**Checking past errors.** An error doesn't stop the check. After a syntax error, every declaration that could be parsed is still checked; a function whose body couldn't be parsed keeps its signature, so its callers are checked against it. A declaration with errors gets no proofs, and an obligation or `check` that mentions one is set aside rather than reported, since it would only repeat the error. Everything else is proved and run, so one mistake doesn't hide the rest.

**Unknown types in messages.** A type the checker hasn't worked out is shown as `_`, or, when it stands for a function's type parameter, as that parameter's name after `?` (`List ?a`), with a note saying whose parameter it is.

## Lexical structure and layout

| Code | Meaning |
|---|---|
| `E0001` | a malformed token: a tab in indentation, an unterminated literal, a bad escape, an invalid number, an unexpected character |
| `E0002` | the file's first line is indented |
| `E0003` | a line returns to an indentation no enclosing block used |
| `E0004` | a bracket is never closed (found at a line that starts a declaration or statement) |
| `E0005` | a `}` in a template that closes no hole (write `}}`) |
| `E0006` | a template's hole still open at the end of the line |

## Syntax

| Code | Meaning |
|---|---|
| `E0100` | the parser expected something else here |
| `E0101` | the file doesn't start with `module name` |
| `E0102` | an indented block where none can start |
| `E0103` | an import after a declaration |
| `E0104` | `export abstract` on something other than an `enum` or `record` |
| `E0105` | `export transparent` on something other than a `fn` |
| `E0106` | a type alias whose first constraint isn't a typing such as `n~Nat` |
| `E0108` | a multi-line `if` without `else` |
| `E0109` | chained comparisons, `a < b < c` |
| `E0110` | `_` outside a pattern |
| `E0112` | `when` without `using` and a scheduler |
| `E0115` | `par` without a tuple of two or more |
| `E0120` | `export` on an instance |
| `E0121` | a class member with a body, or an instance's lemma with a statement |
| `E0122` | a keyword where a name belongs |
| `E0123` | `ghost`, `comptime`, or `own` other than on a function type's parameter, written inside a type |
| `E0124` | a class's type with parameters (`type Elem b`) |

## Names and types

| Code | Meaning |
|---|---|
| `E0201` | a type mismatch |
| `E0202` | a value where a type is expected |
| `E0203` | a parameter's type can't be inferred; give it a constraint |
| `E0204` | an unknown name |
| `E0205` | too many arguments: applying something that isn't a function |
| `E0206` | a module or class has no export or member of that name |
| `E0207` | a record has no field of that name, or the value isn't a record |
| `E0210` | an operator applied to a type it doesn't work on |
| `E0212` | `auto` or `admit` outside a proof |
| `E0213` | a module used as a value |
| `E0214` | `len` not applied to an argument |
| `E0215` | a line whose value would be thrown away (only `Unit` calls may stand alone) |
| `E0220` | no standard-library module of that name |
| `E0221` | an import list names something the module doesn't export |
| `E0222` | an import cycle |
| `E0223` | a file's `module` line doesn't match its path |
| `E0225` | a declaration's head depends on itself |
| `E0226` | two imports with the same qualifier |
| `E0227` | an import from a package that isn't a declared dependency |
| `E0230` | `try` where the block's value isn't the function's result |
| `E0231` | `try` on something other than a `Result` or `Option` |
| `E0232` | `try` in a function whose result can't carry the error |
| `E0240` | a `match`, or a pattern, doesn't cover a case that can occur |
| `E0241` | a constructor of another type in a pattern |
| `E0242` | a constructor pattern with the wrong number of fields |
| `E0243` | a record pattern names a field the record doesn't have |
| `E0244` | an unknown constructor in a pattern |
| `E0245` | a pattern of another type among literal arms |
| `E0246` | a tuple pattern of the wrong size |
| `E0247` | building, matching or reading the fields of an abstract type outside its module |
| `E0248` | a `match` on a type other than a list that takes it apart both with `[]` or `::` and with its constructors |
| `E0260` | a `check` is false |
| `E0261` | a `check` stopped with a run-time error |
| `E0262` | a refinement gained through a type argument of an existing value (`List Int` as `List Nat`) |
| `E0263` | `==` or `!=` on functions, or on values that may contain them |
| `E0264` | a generic function that compares its type parameter's values given a function type |
| `E0270` | a `comptime` argument that depends on a run-time value |
| `E0271` | a function with `comptime` parameters not called with all its arguments |
| `E0272` | `comptime` on a `partial` function or a lemma |
| `E0273` | compile-time evaluation failed |
| `E0280` | an instance of something that isn't a class |
| `E0281` | an instance for a type that isn't a type constructor applied to distinct variables |
| `E0282` | an instance outside the package of its class and of its types (or with a type variable before its package's type) |
| `E0283` | two instances of a class that can match the same types |
| `E0284` | no instance of a class for a type |
| `E0285` | which instance to use can't be decided: the type isn't known there |
| `E0286` | an instance for a type of the wrong kind |
| `E0287` | a class's dictionary built other than by an instance |
| `E0288` | a class's type whose default mentions the class's parameter |
| `E0289` | `forall` outside a named precondition or a lemma's `ensures`, or in a negative place |
| `E0290` | `have` with the wrong number of values for a `forall`'s variables |
| `E0291` | a class's type (`C.Name`) without the types it is for |
| `E0292` | an instance without a type for each of its class's parameters |
| `E0293` | a value shown by a type that isn't known when the program is compiled (it depends on a value known only when the program runs, or holds a field computed from a ghost field) |

## Termination

| Code | Meaning |
|---|---|
| `E0301` | no measure shows the recursion ends |
| `E0302` | a function that isn't `partial` calls a `partial` one |
| `E0303` | a function with `decreasing` used as a value in its own recursion |

## Declarations

| Code | Meaning |
|---|---|
| `E0350` | a name declared twice in a module or class |
| `E0351` | a type alias constraint after the first that isn't a predicate |
| `E0352` | a constructor field without a type |
| `E0353` | a constructor's constraint gives a type to a name that isn't its field |
| `E0354` | a type occurring negatively in its own constructors, or a recursive type as the argument of a type constructor parameter |
| `E0355` | a constraint gives a type to a name that isn't a parameter or the result |
| `E0356` | `__builtin` outside the standard library |
| `E0357` | a lemma's `let` binding more than a name |
| `E0358` | `own` on a type that can't be a resource |
| `E0359` | an abstract type's polarity mark contradicted by its fields |
| `E0360` | a polarity mark on a type that isn't abstract |
| `E0361` | a standard-library builtin the runtime doesn't implement |
| `E0362` | a class function without a type for each parameter and its result |
| `E0363` | an instance member the class doesn't have |
| `E0364` | an instance missing one of the class's functions, or a type the class gives no default for |
| `E0365` | an instance member with other parameters than the class's, or a signature of its own whose types aren't the class's, up to refinement |
| `E0366` | `main`'s signature isn't `args~List String, sys~System, code~ExitCode` |
| `E0367` | a recursive type has no values: every constructor needs a value of the type |
| `E0368` | a function or lemma of a class of several parameters whose parameters' types don't mention one of them, and which doesn't take it as a `ghost Type` parameter |
| `E0369` | a class's function or lemma with a parameter, or a result, named like the class's parameter (except a parameter of type `ghost Type`, which is the class's parameter passed explicitly) |
| `E0370` | a constraint on a class's type that isn't a clause of the type itself (`Ord Item`) or a predicate on one named value of it (`u~Unit, …`) |
| `E0371` | an instance function's own signature that doesn't refine the class's: a precondition the class's don't imply, or a postcondition of the class's it doesn't promise |
| `E0372` | a constraint gives a second type to a parameter, the result or a field that already has one (`x~Int, x~Nat`) |

## Usage: resources and `ghost`

| Code | Meaning |
|---|---|
| `E0401` | a resource used zero times or more than once, or captured by a closure |
| `E0402` | a resource used on some paths and not others |
| `E0403` | a `ghost` value used in code that runs |
| `E0404` | a resource dropped by `_` or by a record pattern |
| `E0405` | a resource put in a cown |
| `E0406` | reading a field would drop a resource in another field |
| `E0407` | indexing an array of resources |
| `E0408` | a `match` guard that uses a resource |

## Proofs

| Code | Meaning |
|---|---|
| `E0450` | an obligation that couldn't be proved, with a counterexample when there is one |
| `E0451` | an obligation outside what the prover handles |
| `E0454` | `have` of a lemma without all its arguments |
| `E0455` | a release build of a program that relies on an `admit` |
| `E0456` | a class used at a refinement alias, whose instance (the type the alias stands for) isn't shown to give values of the alias: a result, or a value it passes to a function parameter |

## Warnings

| Code | Meaning |
|---|---|
| `W001` | a type or constructor name that isn't `UpperCamelCase` |
| `W002` | a function, variable, field or module name that isn't `lower_snake_case` |
| `W003` | a constant name that isn't `SCREAMING_SNAKE_CASE` |
| `W010` | `own` on a type that is a resource anyway |
| `W011` | a `match` on `Seq.uncons xs` that `match xs` with `[]` and `x :: rest` can write |
| `W020` | a declaration nothing reachable uses |
| `W021` | a `match` arm earlier arms already cover |
| `W022` | an arm or branch no value reaches: the facts there contradict each other |
| `W023` | a constructor nothing reachable builds |
| `W024` | a field nothing reachable reads |
| `W030` | a documentation link that names nothing |
| `W031` | a documentation link to something that isn't exported |
| `W032` | a diagnostic in a documentation code block |
| `W033` | a `compile_fail` block that compiles, or fails with another error |
| `W034` | a documentation block whose `main` doesn't exit with `Success` |

`W020` to `W024` aren't reported for the standard library or a package's dependencies. What counts as reachable: from `main` in a program; from the exports in a library; and, in both, from every `check`, lemma and instance. A module with neither `main` nor exports has every declaration counted as used.
