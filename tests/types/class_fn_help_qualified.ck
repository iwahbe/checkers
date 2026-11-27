# The class is in scope only through its module's qualifier: the help
# names its function through it.
module class_fn_help_qualified

import class_names.make

fn by_module_name n -> r : n~Int, r~Int
    make n

fn by_other_name n -> r : n~Int, r~Int
    pick n
