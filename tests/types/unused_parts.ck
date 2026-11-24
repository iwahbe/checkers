# A module of `unused.ck`. Its exports are roots whether it is checked
# alone or imported by a program: a program can also be a library.
module unused_parts

export fn used_part n -> r : n~Int, r~Int
    helper n

# Exported, and `main` doesn't use it: used.
export fn api_part n -> r : n~Int, r~Int
    n

fn helper n -> r : n~Int, r~Int
    n * 2

# Neither `main` nor an export reaches it.
fn stray n -> r : n~Int, r~Int
    n
