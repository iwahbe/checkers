module class_alias_sealed

# A class used at a refinement alias, its instance in another module: the
# prover knows a sealed instance's function by its signature only, so a
# result the body would show is a `Nat` isn't known to be one; a
# `transparent` function's body counts.

import class_home.alias (Make, Build)

fn sealed -> n : n~Nat
    Make.make 5

fn transparent_body -> n : n~Nat
    Build.build 5
