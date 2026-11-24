# Classes whose functions take a class parameter explicitly, as a
# `ghost Type`; their instances are in other modules.
module class_home.pinned

export class Make a
    fn make n a -> r : n~Int, a~ghost Type, r~a

export class Parsable a s
    type Error
    fn parse xs a -> r : Seq s, xs~s, a~ghost Type, r~Result (a, s) Error
