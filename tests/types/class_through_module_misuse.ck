module class_through_module_misuse

# A class named through its module's qualifier is misused as the class
# is: as a value, and its type without the type it is for.

import class_home.sized

fn as_value -> n : n~Int
    let d = sized.Sized
    0

fn without_type p -> n : p~sized.Sized.Part, n~Int
    0
