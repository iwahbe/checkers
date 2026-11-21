module class_type_default_checked

# Defaults are checked at the class, even when no instance uses them.
class Open a
    type Value = Lisst a

class Closed a
    type Value = Missing

# Neither an override nor an omitted assignment can hide an invalid default.
instance Open Int
    type Value = Int

instance Closed Bool

instance Closed Int

class Lowercase a
    type Value = missing a

class NotType a
    type Value = 1

class Incomplete a
    type Value = List

# A kind learned from a method also constrains the default.
class Constructor f
    type Value = f
    fn use x -> n : x~f Int, n~Int
