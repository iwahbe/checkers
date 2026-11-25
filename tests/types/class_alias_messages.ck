module class_alias_messages

# What E0456 says: a tuple's parts, an alias's parameter, an instance of a
# class of two types.

class Two t
    fn two u -> r : u~Int, r~(t, t)

instance Two Int
    fn two u
        (u, u - 1)

fn by_tuple -> p : p~(Nat, Nat)
    two 0

type Below k = n~Nat, n < k

class Make t
    fn make u -> r : u~Int, r~t

instance Make Int
    fn make u -> r : u~Int, r~Int, r >= 0
        if u >= 0 then u else 0

fn by_param -> n : n~Below 7
    make 7

class Conv s h
    fn conv x y -> r : x~s, y~List h, r~h

instance Conv Bool Int
    fn conv x y
        -1

fn by_second -> n : n~Nat
    conv True []
