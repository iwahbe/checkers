module comptime_format

# A bad format string is an error where `fmt` is called (examples/format.ck).

import format (fmt)

fn bad name -> s : name~String, s~String
    fmt "{x} is not a placeholder" name

fn unknown s -> t : s~String, t~String
    fmt s

fn stray -> s : s~String
    fmt "a stray } brace"
