# Importing the module names a class's function through its qualifier,
# with or without the class.
module class_names_by_module

import class_names.make

fn by_module n -> r : n~Int, r~Int
    make.make n + make.pick n

fn by_module_class n -> r : n~Int, r~Int
    make.Make.make n + make.Make.pick n
