module specialize_unbounded

# Compile-time arguments that change on every runtime step would need
# unboundedly many functions: an error, not a hang.

fn walk k src i -> n : k~comptime Nat, src~Bytes, i~Nat, i <= len src, n~Nat
    decreasing len src - i
    if i == len src then k else walk (k + 1) src (i + 1)

fn use src -> n : src~Bytes, n~Nat
    walk 0 src 0
