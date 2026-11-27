module sign_spacing

# A `-` after white space or an opening bracket and glued to what follows
# is a sign; every other `-` subtracts (#657). So `f -1` passes `-1`, a
# line starting with `-1` starts a new line (a block's first line, a
# `match` arm), and a line starting with `- b` continues the one before.

fn sign x -> s : x~Int, s~Int
    if x > 0
        1
    else if x < 0
        -1
    else
        0

fn abs x -> y : x~Int, y~Int
    if x < 0 then -x else x

fn total a b -> s : a~Int, b~Int, s~Int
    a
        - b

fn describe n -> s : n~Int, s~String
    match n
        0  -> "zero"
        -1 -> "minus one"
        _  -> "other"

fn subtract x -> y : x~Int, y~Int
    x -1

check abs -3 == 3
check sign (-5) == -1
check [1, -2] == [1, 0 - 2]
check 2 * -1 == -2
check 3 - -1 == 4
check 5 - 1 == 4
check total 5 3 == 2
check describe -1 == "minus one"
