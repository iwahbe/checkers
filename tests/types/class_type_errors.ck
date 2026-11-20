module class_type_errors

# What is wrong with a class's type, and with using it.

class Display a
    type Options = NoOptions
    fn display x os -> s : x~a, os~List Options, s~String

enum NoOptions

record Money
    cents~Int

enum MoneyOption
    Cents
    Whole

instance Display Money
    type Options = MoneyOption
    fn display m os
        "m"

instance Display Int
    fn display x os
        format x

# A type with no default, and a default mentioning the class's parameter.
class Sized a
    type Unit
    type Wrapped = List a
    fn size x -> n : x~a, n~Int

instance Sized Int
    fn size x
        1

# A type the class doesn't have.
instance Sized Bool
    type Unit = Int
    type Extra = Int
    fn size x
        1

# `Int`'s options are `NoOptions`.
fn by_default -> s : s~String
    display 5 [Cents]

# At a type parameter, only options it was given.
fn generic x -> s : Display a, x~a, s~String
    display x [Cents]

fn rigid x -> o : Display a, x~a, o~Display.Options a
    Cents

# No clause for `a`.
fn no_clause x -> os : x~a, os~List (Display.Options a)
    []

# Without the type it is for.
fn bare -> t : t~Type
    Display.Options

# The type is never known.
fn never -> s : s~String
    let f = \v -> display v []
    "?"
