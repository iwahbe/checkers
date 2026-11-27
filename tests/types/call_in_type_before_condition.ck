# A call in a type relies only on the conditions written before its
# typing: E0450 where the condition it needs comes after it.
module call_in_type_before_condition

fn pos k -> r : k~Int, k > 0, r~Int
    k

record At n : n~ghost Int
    v~Int, v == n

fn in_result k -> r : k~Int, r~At (pos k), k > 0
    At (pos k)
