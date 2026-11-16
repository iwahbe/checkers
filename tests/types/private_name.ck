# A name a module declares but doesn't export: the error says so, imported
# by name, used unqualified or qualified (E0204, E0206, E0221).
module private_name

import private.shapes (area, perimeter)
import private.shapes as s

check area 2 3 == 6
check perimeter 2 3 == 10
check s.perimeter 2 3 == 10

fn corner -> c : c~s.Corner
    s.Corner 0 0
