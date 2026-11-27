module class_module

# A class named through its module: its members, as for the class.
import std.parse

fn member xs -> r : xs~String, r~Int
    parse.Parsable.‸
