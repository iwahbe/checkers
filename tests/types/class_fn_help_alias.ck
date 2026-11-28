# The qualifier in the help is the import's alias.
module class_fn_help_alias

import class_names.make as m

fn by_name n -> r : n~Int, r~Int
    pick n
