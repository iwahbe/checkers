module format_unimported

# `format`, `display` and `debug` are `std.string`'s, imported like its
# other names: without an import they are unknown, and the help says
# which import.

fn tag n -> s : n~Int, s~String
    format"n is {n}"

fn shown n -> s : n~Int, s~String
    display n [] ++ debug n
