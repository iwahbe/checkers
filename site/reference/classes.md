# Classes

A class names functions and lemmas that a type may provide: an order (`Ord`), addition (`Add`), mapping over a container (`Functor`). An **instance** provides them for one type, and proves the lemmas. Code generic over a type with a class constraint can use them, and gets them for the caller's type at each call. A class's lemmas are its laws: generic code may rely on them, because every instance has proved them.

## Declaring a class

```text
class  ::= 'class' Uname lname NL INDENT { member } DEDENT
member ::= 'fn' lname { lname } '->' lname ':' constraints NL
         | 'lemma' lname { lname } [ ':' constraints ] NL INDENT 'ensures' expr NL DEDENT
```

A class has one parameter, and lists its members: functions, each with a signature giving the type of every parameter and of the result (E0362), and lemmas, each with a statement. Members have no bodies. A lemma that follows from the members isn't part of the class: write it outside, as an ordinary lemma with the class as a constraint.

```checkers
class Size a
    fn size x -> n : x~a, n~Nat
    lemma size_pos x : x~a
        ensures size x >= 0
```

A member is named `C.f` (`Size.size`), or `f` alone where the class is in scope or imported unqualified. A member's parameter written `own` (`x~own a`) may receive a resource ([Capabilities](effects.md#resources)).

## Instances

```text
instance ::= 'instance' Uname type [ ':' constraints ] NL INDENT { member } DEDENT
```

An instance gives each of the class's functions a body for one type (E0364 if one is missing, E0363 for one the class doesn't have, E0365 if its parameters don't match the class's), and may give each lemma a `proof`; without one, Z3 proves it, as for any lemma. A proof by induction may start with `decreasing e`, as any lemma's may ([Termination](termination.md#lemmas)). The signatures are the class's, at the instance's type. After `:`, the constraints are what the instance needs of its type's parameters.

```checkers
record Version
    major~Nat
    minor~Nat

# Versions in order: by major number, then minor. `Ord`'s lemmas
# (`trans`, `total`, `antisym`) are proved here by Z3, without help.
instance Ord Version
    fn le v w
        v.major < w.major or (v.major == w.major and v.minor <= w.minor)

check le (Version 1 2) (Version 1 10)
```

Inside an instance, a member's name is the instance's own: a function recursing on the instance's type calls itself, checked for termination like any recursion. The class's function at another type is written `C.f`.

```checkers
class Size a
    fn size x -> n : x~a, n~Nat

instance Size Bool
    fn size b
        1

# `size` here is this instance's own, on lists; an element's is `Size.size`.
instance Size (List a) : Size a
    fn size xs
        match xs
            []        -> 0
            x :: rest -> Size.size x + size rest

check size [True, False] == 2
check size [[True], [], [False, True]] == 3
```

### Coherence

There is at most one instance of a class for a type, wherever it is used:

- an instance is for a type constructor applied to distinct type variables (`List a`, `Pair a`, `Int`), not for a type such as `List Int` (E0281), and of the kind the class expects (E0286);
- it is declared in the package of the class or of the type, never in a third (E0282), as Rust's orphan rule asks;
- no two instances of a class have the same type constructor (E0283).

An instance isn't exported (E0120): it applies wherever its module is loaded. A second order on a type is given through a wrapper type with its own instance, or by sorting with a key or a comparison (`list.sort_as`, `list.sort_by`).

## Using a class

A class applied to a type, in a signature, is a constraint: `Ord a` means the function works for any `a` with an `Ord` instance.

```checkers
fn larger x y -> r : Ord a, x~a, y~a, r~a, le x r and le y r
    have total x y
    have refl x
    have refl y
    if le x y then y else x

check larger "fig" "apple" == "fig"
check larger 3 7 == 7
```

At each call, once the types are known, the instance is found: a constraint of the calling function for that type, or the instance for the type's constructor, whose own constraints are found the same way. E0284 if there is none; E0285 if the type isn't known there.

**At run time**, each class constraint is an argument: a record of the instance's functions. Lemmas are erased. **To the prover**, a class's function at a type parameter is an unknown function, about which it knows the class's lemmas, brought in with `have` (`have total x y`, or `have Ord.total x y`); at a known type it is the instance's function, whose body is visible everywhere.

## Operators

On numbers, the arithmetic operators and comparisons are built in. On other types, and on type parameters, they go through the prelude's classes:

| Written | Means | Class |
|---|---|---|
| `x + y` | `add x y` | `Add` |
| `x - y` | `sub x y` | `Sub` |
| `x * y` | `mul x y` | `Mul` |
| `-x` | `neg x` | `Neg` |
| `x <= y` | `le x y` | `Ord` |
| `x >= y` | `le y x` | `Ord` |
| `x < y` | `not (le y x)` | `Ord` |
| `x > y` | `not (le x y)` | `Ord` |

`Monoid` adds `zero` and the laws `assoc`, `zero_add` and `add_zero`, stated with `+`. `Int` has an instance of each, so generic code works on numbers. With no instance, an operator is E0210.

```checkers
record Money
    cents~Int

instance Add Money
    fn add a b
        Money (a.cents + b.cents)

check (Money 150 + Money 75).cents == 225
```

## Classes over type constructors

A class's parameter is a type constructor when its members apply it: in `Functor f`, `xs~f a` makes `f` of kind `Type -> Type`. An instance is then for a type constructor missing that many parameters (`instance Functor List`, `instance Functor (Pair k)`). A member may have type parameters of its own (`a` and `b` in `fmap`).

```checkers
fn doubled xs -> ys : Functor f, xs~f Int, ys~f Int
    fmap (\x -> x * 2) xs

check doubled [1, 2] == [2, 4]
check doubled (Some 5) == Some 10
```

`f a` is matched against a type such as `List Int` with `f` as `List` and `a` as `Int`. A recursive type can't be passed as the argument of a type constructor parameter (E0354): nothing says how `f` uses its argument, so it could use it negatively.

## The prelude's classes

| Class | Members | Instances in the prelude |
|---|---|---|
| `Ord a` | `le`; lemmas `trans`, `total`, `antisym` | `Int` (and so `Nat`, `Char` and the fixed-width numbers), `Bool` (`False` first), `String` (by scalar values), `List a` (lexicographic), `Option a` (`None` first) |
| `Add a`, `Sub a`, `Mul a`, `Neg a` | `add`, `sub`, `mul`, `neg` | `Int` |
| `Monoid a` | `zero`; lemmas `assoc`, `zero_add`, `add_zero` | `Int` |
| `Functor f` | `fmap`; lemmas `fmap_id`, `fmap_comp` | `List`, `Option`; `Array` in `std.array` |

The prelude also has the lemma `refl` (`le x x`), which follows from `total`.
