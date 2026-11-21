module class_type_parameter_default_import

import defaults.source (Wrapped)
import defaults.source as source

record Box a
    other~List a

instance Wrapped Int
    fn wrap renamed
        source.Box renamed

instance Wrapped (List b)
    fn wrap xs
        source.Box xs

fn concrete -> result : result~source.Box Int
    source.wrap 1
