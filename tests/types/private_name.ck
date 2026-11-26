# A name a module declares but doesn't export: the error says so, imported
# by name, used unqualified or qualified (E0204, E0206, E0221). The module is
# in this package, so the help says what to change there: for a constructor
# of an abstract type, dropping `abstract`; for a constructor of a type that
# isn't exported, exporting the type.
module private_name

import private.shapes (area, perimeter, Size)
import private.shapes as s

check area 2 3 == 6
check perimeter 2 3 == 10
check s.perimeter 2 3 == 10

fn corner -> c : c~s.Corner
    s.Corner 0 0

fn measured -> z : z~Size
    Measured 3

fn measured_qualified -> z : z~Size
    s.Measured 3

check s.Square 2 == s.Square 2
