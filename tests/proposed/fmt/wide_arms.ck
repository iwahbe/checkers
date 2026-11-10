# Proposed: an arm with a guard doesn't take part in alignment.
module wide_arms

fn value src i depth : src~Bytes, i~Nat, depth~Nat
    match peek src i
        None -> 0
        Some 'n' -> 1
        Some '[' if depth >= MAX_DEPTH -> 2
        Some '[' ->
            3
        Some b -> 4
