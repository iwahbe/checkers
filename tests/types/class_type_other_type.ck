module class_type_other_type

# In a class with a type, a class function used in a member's signature
# finds its instance by its arguments: `width 0` is `Int`'s at every
# instance. Only where they don't tell (`valid os`) is it the instance's.

class Display a
    type Options = NoOptions
    fn width x -> n : x~a, n~Int
    fn valid os -> b : os~List Options, b~Bool
    fn display x os -> s : x~a, os~List Options, width 0 >= 0, valid os, s~String

enum NoOptions

instance Display Int
    fn width x
        1
    fn valid os
        True
    fn display x os
        "i"

instance Display Bool
    fn width x
        1
    fn valid os
        True
    fn display x os
        "b"
