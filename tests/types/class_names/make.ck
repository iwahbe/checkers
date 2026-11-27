# A class whose function has its module's name, and one whose doesn't.
module class_names.make

export class Make t
    fn make n -> r : n~Int, r~t
    fn pick n -> r : n~Int, r~t

instance Make Int
    fn make n
        n
    fn pick n
        n + 1
