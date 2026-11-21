module class_param_name

# A member's parameter named like the class's parameter.

class ByParam a
    fn by_param a -> r : a~a, r~Int

class ByResult a
    fn by_result x -> a : x~Int, a~Int

class ByLemma a
    fn ok x -> r : x~a, r~Bool
    lemma by_lemma a : a~a
        ensures ok a

# Of type `ghost Type`, it is the class's parameter, passed explicitly.
class ByType a
    fn by_type a -> r : a~ghost Type, r~Int

class BySecond s t
    fn by_second x t -> r : x~s, t~ghost Type, r~t

instance ByType Int
    fn by_type a
        0

check by_type Int == 0

# The instance gives the member anyway: nothing more is reported.
instance ByParam Int
    fn by_param a
        0
