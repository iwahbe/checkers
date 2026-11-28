# Only the class is imported: a bare use of its function is not in scope,
# and the help names it through the class.
module class_fn_help_imported

import class_names.make (Make)

fn by_module_name n -> r : n~Int, r~Int
    make n

fn by_other_name n -> r : n~Int, r~Int
    pick n
