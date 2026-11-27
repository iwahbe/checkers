module class_through_module

# A class named through its module's qualifier, `sized.Sized`, is the
# class, as `m.T` is a type: its function, its lemma, its type, and a
# clause.

import class_home.sized

fn by_member b -> n : b~Bool, n~Int
    sized.Sized.size b

fn by_type p -> n : p~sized.Sized.Part Bool, n~Int
    p

fn by_clause x -> n : sized.Sized a, x~a, n~Int, n >= 0
    have sized.Sized.pos x
    sized.size x

check by_member True == 1
