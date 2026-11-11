module phases

# Each phase's diagnostics, then its `done` line (§15.5): a warning while
# names are resolved, a true `check` (none in that phase), and an unproven
# postcondition.
import lib.helper

type small = n~Nat, n < 10

fn bigger x -> r : x~Nat, r~Nat, r > 5
    x + helper.one

check bigger 1 == 2
