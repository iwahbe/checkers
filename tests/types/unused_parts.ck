# A module of `unused.ck`. Checked alone it is a library: its exports are
# used. Imported by a program, only what `main` reaches is.
module unused_parts

export fn used_part n -> r : n~Int, r~Int
    helper n

export fn unused_part n -> r : n~Int, r~Int
    n

fn helper n -> r : n~Int, r~Int
    n * 2
