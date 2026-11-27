# Importing a class's function by name makes it a bare name, without the
# class.
module class_names_by_function

import class_names.make (make)

fn by_function n -> r : n~Int, r~Int
    make n
