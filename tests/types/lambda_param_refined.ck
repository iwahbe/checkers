module lambda_param_refined

# A lambda's parameter has the refinement of its type even when that type is
# only known from a later argument: `c` here is a `Char`, so `from_char c`
# meets its precondition (found while writing std.string's checks, M18).
import std.list
import std.string

fn dotted_all cs -> s : cs~List Char, s~String
    list.join "" (list.map (\c -> string.from_char c ++ ".") cs)

check dotted_all [c'a', c'é'] == "a.é."
check list.join "" (list.map (\c -> string.from_char c ++ ".") (string.chars "aé")) == "a.é."
check string.concat_map (\c -> string.from_char c ++ ".") "aé" == "a.é."
