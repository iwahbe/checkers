module negative_arm

# A line starting with an operator continues the logical line before it
# only when it is indented further than that line's first: a `match` arm
# `-1 -> …` at the arms' indentation is an arm of its own (§9.1).

fn describe n -> s : n~Int, s~String
    match n
        0  -> "zero"
        -1 -> "minus one"
        _  -> "other"

fn total a b -> s : a~Int, b~Int, s~Int
    a
        - b

check describe (-1) == "minus one"
check describe 0 == "zero"
check total 5 3 == 2
