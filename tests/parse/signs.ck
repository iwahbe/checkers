# Which `-` is a sign (D169): after white space or an opening bracket, and
# glued to what follows. Every other `-` subtracts.
module signs

check 5-1
check 5 - 1
check f -1
check f - 1
check 2*-1
check x - -1
check [1,-2]
check (-x)
check (- x)
check (-)
check -f x
check f -x.y
check a
    -1
