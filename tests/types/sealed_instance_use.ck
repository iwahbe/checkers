module sealed_instance_use

# Sealing (#537): an exported function stays sealed when an instance's
# function, whose body every importer sees, calls it.

import sealed_instance_lib (Meters, sign)

lemma by_body m : m~Meters, m.value < 0
    ensures sign m == "-"
