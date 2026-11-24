module instance_pinned_other_module

# Instances of classes from another module whose functions take the
# class's parameter explicitly, as a `ghost Type`.

import class_home.pinned (Make, Parsable)
import class_home.mark (Mark)

record Flag
    on~Bool

instance Make Flag
    fn make n a
        Flag (n > 0)

check (Make.make 3 Flag).on

# Several parameters, a type and a clause.
instance Parsable Flag s
    type Error = Unit
    fn parse xs a
        match xs
            x :: rest -> Ok (Flag True, rest)
            []        -> Err ()

# An instance declared in a third module.
check (Make.make 3 Mark).on
check not (Make.make 0 Mark).on
