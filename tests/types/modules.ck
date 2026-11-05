module modules

import nothing_here
import list (no_such_thing)

fn uses_unimported -> s : s~String
    string.from_chars []

fn qualified_missing -> n : n~Nat
    list.nope

fn builtin_body -> n : n~Nat
    __builtin
