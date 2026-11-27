module known_own_call_imported

# An imported module's lemma knows the value of a call of that module's
# own function, as when it is the module checked.

import known_own_call (by_value)

export lemma uses_import
    ensures True
    proof
        have by_value
