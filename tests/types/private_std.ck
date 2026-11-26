# A name a standard-library module declares but doesn't export: the error
# says it is private and suggests no change to the standard library
# (E0204, E0206, E0221).
module private_std

import std.list (reverse_onto)
import std.list

check reverse_onto [1] [] == [1]
check list.reverse_onto [1] [] == [1]
