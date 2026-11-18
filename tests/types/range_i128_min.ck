# Arithmetic whose result is the least 128-bit integer: its range is that
# one value, and the value is right.
module range_i128_min

export fn low -> r : r~Int
    -170141183460469231731687303715884105727 - 1

check low < 0
check low + 1 == -170141183460469231731687303715884105727
check format low == "-170141183460469231731687303715884105728"
