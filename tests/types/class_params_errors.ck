module class_params_errors

import std.string (debug)

# What is wrong with a class of several parameters, its instances, and
# their uses.

record Format
    prefix~String

record Plain
    sep~String

class Hole s h
    fn hole tag x -> r : tag~s, x~h, r~String

instance Hole Format a
    fn hole f x
        f.prefix

instance Hole Plain String
    fn hole p x
        x

instance Hole Plain Int
    fn hole p x
        debug x

# Overlaps `Hole Format a`: both match `Format` and `String`.
instance Hole Format String
    fn hole f x
        x

# The first type is a variable.
instance Hole a Bool
    fn hole t x
        "?"

# A type for each parameter.
instance Hole Plain
    fn hole p x
        "?"

# A variable twice.
instance Hole (List a) a
    fn hole xs x
        "?"

# A function that doesn't mention `h`: a use couldn't tell the instance.
class Pick s h
    fn pick tag -> r : tag~s, r~h

# No instance for `Plain` and `Bool`.
fn no_instance -> r : r~String
    hole (Plain ";") True

# The hole's type never becomes known.
fn never_known -> r : r~String
    let f = \x -> hole (Plain ";") x
    "x"

# No clause for the type parameters.
fn no_clause t x -> r : t~s, x~h, r~String
    hole t x

class Fill s h
    type Options

fn without_types -> t : t~Type
    Fill.Options Plain
