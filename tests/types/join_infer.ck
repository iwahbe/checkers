module join_infer

# The types of the futures given to `join` are inferred: `futures ?ts`
# against a tuple of futures picks `ts` arm by arm (#659).

import std.future (Future)
import std.future

fn one a -> r : a~Future Nat, r~Nat
    future.join a

fn three a b c -> r : a~Future Nat, b~Future String, c~Future Int, r~(Nat, String, Int)
    future.join (a, b, c)

fn sum a b -> r : a~Future Nat, b~Future Nat, r~Nat
    let (x, y) = future.join (a, b)
    x + y

# Not futures: nothing for `ts` to be.
fn not_futures n -> r : n~Nat, r~Nat
    let (x, y) = future.join (n, n)
    x
