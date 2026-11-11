module types

# A type error: the later phases do nothing, but each still ends with `done`.
# The error's notes and help line, and a diagnostic in an imported module.
import lib.broken

fn g -> r : r~String
    1 + "a"
