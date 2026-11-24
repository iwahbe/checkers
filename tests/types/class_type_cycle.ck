module class_type_cycle

# An instance's type defined through itself.

class Display a
    type Options
    fn display x os -> s : x~a, os~List Options, s~String

record Money
    cents~Int

instance Display Money
    type Options = Display.Options Money
    fn display m os
        "m"

record Coin
    value~Int

record Note
    value~Int

instance Display Coin
    type Options = Display.Options Note
    fn display c os
        "c"

instance Display Note
    type Options = Display.Options Coin
    fn display n os
        "n"
