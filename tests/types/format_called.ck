module format_called

# `format` is a template's tag, not a function of a value: called on one,
# it is an error whose help shows the ways to show the value.

import std.string (format)

fn called n -> s : n~Int, s~String
    format (n + 1)
