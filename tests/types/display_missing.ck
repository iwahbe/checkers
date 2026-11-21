module display_missing

# A hole of `format` takes a value with a `Display` instance: a type with
# none is E0284 at the value, and so is a type parameter without the
# clause `Display a`. `debug` needs no clause.

import std.string (format, debug)

record Point
    x~Int

fn at_type p -> s : p~Point, s~String
    format"at {p}"

fn at_param x -> s : x~a, s~String
    format"at {x}"

fn by_debug x -> s : x~a, s~String
    format"at {debug x}"
