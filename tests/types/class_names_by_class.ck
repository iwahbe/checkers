# Importing a class names its functions through it, `Make.make`; a bare
# `make` or `pick` is not in scope.
module class_names_by_class

import class_names.make (Make)

class Local t
    fn local n -> r : n~Int, r~t

instance Local Int
    fn local n
        n

fn by_class n -> r : n~Int, r~Int
    Make.make n

fn by_bare n -> r : n~Int, r~Int
    make n

fn by_bare_other n -> r : n~Int, r~Int
    pick n

fn by_local n -> r : n~Int, r~Int
    local n + Local.local n

fn by_prelude x y -> r : x~Int, y~Int, r~Bool
    le x y and Ord.le x y
