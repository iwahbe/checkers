module class_through_module

# A class named through its module's qualifier, `sized.Sized`, is the
# class, as `m.T` is a type: its function, its lemma, its type, a clause,
# and an instance's class and context.

import class_home.sized

fn by_member b -> n : b~Bool, n~Int
    sized.Sized.size b

fn by_type p -> n : p~sized.Sized.Part Bool, n~Int
    p

fn by_clause x -> n : sized.Sized a, x~a, n~Int, n >= 0
    have sized.Sized.pos x
    sized.size x

record Box a
    v~a

instance sized.Sized (Box a) : sized.Sized a
    type Part = Int
    fn size b
        sized.size b.v
    lemma pos b
        proof
            have sized.Sized.pos b.v

fn by_instance -> n : n~Int
    sized.size (Box True)

check by_member True == 1
check by_instance == 1
