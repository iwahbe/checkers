# Importing the module names a class's function through its qualifier.
module class_names_by_module

import class_names.make

fn by_module n -> r : n~Int, r~Int
    make.make n + make.pick n
