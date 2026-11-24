module class_type_lemma_param

# A class's lemma that mentions the class's type, proved at instances
# for types with parameters.

class C s
    type E
    fn get x -> r : x~s, r~Option E
    lemma got x : x~s
        ensures get x == None

instance C (List a)
    type E = a
    fn get x
        None

instance C (Option a)
    type E = Bool
    fn get x
        None
