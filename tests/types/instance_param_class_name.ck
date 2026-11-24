module instance_param_class_name

# An instance's parameter may have the name of the class's parameter: in
# the instance's signatures it is still the parameter, not the type.

class Sized s
    fn size xs -> n : xs~s, n~Nat
    fn half xs -> r : xs~s, r~Nat, r <= size xs

record Box
    n~Nat

instance Sized Box
    fn size s
        s.n
    fn half s
        s.n / 2

check half (Box 5) == 2
