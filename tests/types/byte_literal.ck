module byte_literal

# `'x'` is a `U8` literal and `c'x'` a `Char` literal (D19); both mix freely
# with `Nat` (D38).

fn shout s -> r : s~String, r~String
    s ++ "!"

fn next b -> n : b~U8, n~Nat
    b + 1

check next 'a' == 98
check 'a' + 1000 == 1097
check c'a' + 1 == 98
check [c'é'] == [c'é']

fn wrong -> r : r~String
    shout 'a'

fn also_wrong -> r : r~String
    shout c'a'
