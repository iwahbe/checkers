module class_through_module_misuse

# A class named through its module's qualifier is misused as the class
# is: as a value, its type without the type it is for, and an instance
# or a context of a name the module doesn't export.

import class_home.sized

fn as_value -> n : n~Int
    let d = sized.Sized
    0

fn without_type p -> n : p~sized.Sized.Part, n~Int
    0

record Box
    v~Int

instance sized.Missing Box
    fn size b
        1

record Pair a
    left~a

instance sized.Sized (Pair a) : sized.Missing a
    type Part = Int
    fn size p
        1
