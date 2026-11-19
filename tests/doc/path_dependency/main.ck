# main.ck — uses a path dependency.
module main

import geometry.circle (diameter)

# Twice two.
#
# ```
# #! import geometry.circle (diameter)
# check main.four == diameter 2
# ```
export fn four -> n : n~Nat
    diameter 2
