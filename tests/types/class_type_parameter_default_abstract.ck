module class_type_parameter_default_abstract

class Wrapped a
    type Value = List a
    fn wrap x -> y : x~a, y~Value

fn generic x -> xs : Wrapped a, x~a, xs~List a
    wrap x
