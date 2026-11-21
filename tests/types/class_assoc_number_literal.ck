module class_assoc_number_literal

class Show a
    fn show x -> r : x~a, r~String

instance Show Int
    fn show x
        "i"

class Make s
    type Made
    fn made x -> r : x~s, r~Made

instance Make Int
    type Made = Int
    fn made x
        x

check show (made 1) == "i"
