module template_generic

# A tag whose formatter is a type parameter, with the classes' clauses.

import std.string (Template, Hole)

fn wrap mk x -> r : Template s, Hole s String, mk~(Nat -> Nat -> s), x~String, r~Template.Result s
    mk"<{x}>"
