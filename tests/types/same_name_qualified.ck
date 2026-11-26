# Two types of the same name, neither imported unqualified, are shown as
# this module refers to each: its own by its name, others by the qualifier
# of their module's import.
module same_name_qualified

import same_name.a
import same_name.b

record T
    x~Nat

fn declared t -> r : t~b.T, r~T
    t

fn both t -> r : t~a.T, r~b.T
    t
