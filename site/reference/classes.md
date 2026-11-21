# Classes

A class names functions and lemmas that a type may provide: an order (`Ord`), addition (`Add`), mapping over a container (`Functor`). An **instance** provides them for one type, and proves the lemmas. Code generic over a type with a class constraint can use them, and gets them for the caller's type at each call. A class's lemmas are its laws: generic code may rely on them, because every instance has proved them.

## Declaring a class

```text
class  ::= 'class' Uname lname { lname } NL INDENT { member } DEDENT
member ::= 'type' Uname [ '=' type ] NL
         | 'fn' lname { lname } '->' lname ':' constraints NL
         | 'lemma' lname { lname } [ ':' constraints ] NL INDENT 'ensures' expr NL DEDENT
```

A class has a type parameter, or several ([Classes of several types](#classes-of-several-types)), and lists its members: types that each instance gives ([A class's types](#a-classs-types)), functions, each with a signature giving the type of every parameter and of the result (E0362), and lemmas, each with a statement. Members have no bodies. A lemma that follows from the members isn't part of the class: write it outside, as an ordinary lemma with the class as a constraint.

```checkers
class Size a
    fn size x -> n : x~a, n~Nat
    lemma size_pos x : x~a
        ensures size x >= 0
```

A member is named `C.f` (`Size.size`), or `f` alone where the class is in scope or imported unqualified. A member's parameter written `own` (`x~own a`) may receive a resource ([Capabilities](effects.md#resources)).

## Instances

```text
instance ::= 'instance' Uname type { type } [ ':' constraints ] NL INDENT { member } DEDENT
member   ::= 'type' Uname '=' type NL
           | 'fn' lname { lname } NL INDENT block DEDENT
           | 'lemma' lname { lname } [ NL INDENT 'proof' NL INDENT block DEDENT DEDENT ]
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

- an instance is for a type constructor applied to distinct type variables (`List a`, `Pair a`, `(a, b)`, `Int`, `Bool`, `()`), not for a type such as `List Int` (E0281), and of the kind the class expects (E0286); `Unit` names `()`, so `instance Show Unit` is that instance too, but an instance is never for another type alias; `(a, b, c)` is `(a, (b, c))`, so `instance C (a, b)` covers every tuple of two or more parts, `b` being the rest, and an instance for `(a, b, c)` is E0281;
- it is declared in the package of the class or of the type, never in a third (E0282), as Rust's orphan rule asks;
- no two instances of a class have the same type constructor (E0283).

A class of several types has its own rules ([Classes of several types](#classes-of-several-types)).

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

## A class's types

A class may let each instance choose a type. `type Name` declares one; inside the class, its members use it by its bare name, anywhere a type may appear, a precondition included. `type Name = T` gives it a default, used by every instance that doesn't give its own; a default may mention the class's parameters, which are replaced by the instance's types. An explicit type overrides the default; with an unknown dictionary in generic code, the type remains abstract. A class's type takes no parameters of its own (E0124).

```checkers
# How to show a value; each type says which options its display takes.
class Display a
    type Options = NoOptions
    fn display x os -> s : x~a, os~List Options, s~String

# No constructors: the only list of options is `[]`.
enum NoOptions

record Money
    cents~Int

enum MoneyOption
    Cents
    Whole

instance Display Money
    type Options = MoneyOption
    fn display m os
        match os
            [Cents] -> format m.cents ++ "¢"
            _       -> "$" ++ format (m.cents / 100)

# `Options` is `NoOptions` here.
instance Display Int
    fn display x os
        format x

check display (Money 1250) [Cents] == "1250¢"
check display 7 [] == "7"
```

An instance gives the type with `type Name = T`, or leaves it out to take the default (E0364 if there is none). In the instance's signatures, `Name` is that type.

Outside the class, the type is `C.Name t`: `Display.Options Money`, or `Display.Options a` under the constraint `Display a` (E0284 without one; `C.Name` alone is E0291). At a type whose instance is known, it is that instance's type: `Display.Options Money` is `MoneyOption`, to the type checker and the prover alike. At a type parameter, it is a type of its own, equal only to itself, so generic code can pass `[]`, or options it was given, and nothing else:

```checkers
class Display a
    type Options = NoOptions
    fn display x os -> s : x~a, os~List Options, s~String

enum NoOptions

# Any `Display` type, without options.
fn plain x -> s : Display a, x~a, s~String
    display x []

# Any `Display` type, with options the caller chose for it.
fn twice x os -> s : Display a, x~a, os~List (Display.Options a), s~String
    display x os ++ display x os

# A pair shows both values with the options of their type.
record Pair a
    first~a
    second~a

instance Display (Pair a) : Display a
    type Options = Display.Options a
    fn display p os
        Display.display p.first os ++ ", " ++ Display.display p.second os
```

A class's type doesn't tell which instance it is: `Int` and another type may both take `NoOptions`. So where the type isn't known yet, `display v [Cents]` doesn't decide what `v` is; the options are checked once `v`'s type is known from elsewhere, and if it never is, the call is E0285.

At run time the type is erased, but an array of it, made in generic code, is laid out as the instance's type is: the instance's record of functions carries what the layout needs.

## Classes of several types

A class may take several type parameters, when what is allowed depends on the types together. Here a formatter decides which types of values its holes accept: one takes anything with a display, one only strings, one strings and ints.

```checkers
class Hole s h
    fn hole tag x -> r : tag~s, x~h, r~String

class Show a
    fn show x -> s : x~a, s~String

instance Show Int
    fn show x
        format x

record Format
    prefix~String

record Page
    title~String

record Plain
    sep~String

# Any type with a `Show`.
instance Hole Format a : Show a
    fn hole f x
        f.prefix ++ show x

# Only strings.
instance Hole Page String
    fn hole p x
        p.title ++ x

# Strings and ints, nothing else.
instance Hole Plain String
    fn hole p x
        x

instance Hole Plain Int
    fn hole p x
        format x ++ p.sep

fn fill t x -> r : Hole s h, t~s, x~h, r~String
    hole t x

check hole (Format "#") 3 == "#3"
check hole (Page "p: ") "x" == "p: x"
check fill (Plain ";") 4 == "4;"
```

Each function and lemma of the class mentions every one of its parameters in its parameters' types (E0368): a use finds the instance from the types of its arguments.

An instance gives a type for each parameter (E0292). Each is a type constructor applied to distinct type variables, as for one parameter, or a bare type variable, except the first (E0281). An instance may be declared in the package of the class, or in the package of one of its types, provided no type before it is a bare variable (E0282), as Rust's orphan rule asks: `instance Hole Format Mine` may be in `Mine`'s package even though `Hole` and `Format` are another package's, but `instance Rel Format a Mine` may not, since `a` comes first. Two instances of a class whose types could match the same types overlap (E0283): `Hole Format a` and `Hole Format String` would, `Hole Format a` and `Hole Page String` don't.

At a use, an instance is chosen once the use's types are known wherever the instance names a type constructor; where it has a variable, the type needn't be known yet. A use at `Format` chooses `Hole Format a` at once. A use at `Page` waits until the value's type is known, even though `Hole Page String` is `Page`'s only instance: another module, loaded later, may give `Page` another, and a use shouldn't mean something different depending on what is loaded. If the type never becomes known, the use is E0285. With no instance that can match, as for `Plain` and `Bool`, it is E0284.

A class's type takes a type for each parameter outside the class: `Hole.Options s h` for a `type Options` declared in `Hole`.

## The prelude's classes

| Class | Members | Instances in the prelude |
|---|---|---|
| `Ord a` | `le`; lemmas `trans`, `total`, `antisym` | `Int` (and so `Nat`, `Char` and the fixed-width numbers), `Bool` (`False` first), `String` (by scalar values), `List a` (lexicographic), `Option a` (`None` first) |
| `Add a`, `Sub a`, `Mul a`, `Neg a` | `add`, `sub`, `mul`, `neg` | `Int` |
| `Monoid a` | `zero`; lemmas `assoc`, `zero_add`, `add_zero` | `Int` |
| `Functor f` | `fmap`; lemmas `fmap_id`, `fmap_comp` | `List`, `Option`; `Array` in `std.array` |

The prelude also has the lemma `refl` (`le x x`), which follows from `total`.
