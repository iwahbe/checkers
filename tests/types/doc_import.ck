# A module's doc comment blocks import it (D164): what it exports, by name,
# with no import line:
#
#     check double 2 == 4
#     check TWO == 2
#
# A block that imports it itself is left as it is:
#
#     import doc_import (double)
#     check double 1 == 2
#
# A name it doesn't export isn't brought in, so this is reported:
#
#     check halve 4 == 2
module doc_import

export fn double n -> m : n~Nat, m~Nat
    n + n

export let TWO = 2

fn halve n -> m : n~Nat, m~Nat
    n / 2

check halve 4 == 2
