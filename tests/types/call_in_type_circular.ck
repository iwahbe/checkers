# A condition can't justify a call it depends on: E0450 where two
# refinements' calls would each be justified only by the other.
module call_in_type_circular

fn pos k -> r : k~Int, k > 0, r~Int
    k

fn circular k a b : k~Int, a~(x~Int, pos k > 0), b~(y~Int, pos k > 0)
    ()

# Fine: `a`'s refinement calls nothing, so `b`'s call relies on it.
fn one_way k a b : k~Int, a~(x~Int, k > 0), b~(y~Int, pos k > 0)
    ()
