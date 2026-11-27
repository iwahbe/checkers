# hint.ck — hints to the compiler, for measuring and testing the code it
# makes.
module std.hint

# `x`, as a value the compiler never knows when compiling. A test or a
# benchmark gives its inputs through it, so that what it measures is the
# code that runs on them, not values computed while compiling. The prover
# still knows that the result is `x`.
export fn blackbox x -> r : x~a, r~a, r == x
    __builtin
