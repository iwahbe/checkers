module types

# A type error and nothing else to check: each later phase still ends with `done`.
# The error's notes and help line, and a diagnostic in an imported module.
import lib.broken

fn g -> r : r~String
    1 + "a"
