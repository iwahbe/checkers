module operators

check (+) 1 2 == 1 + 2
check map (+ 1) xs == map (1 +) xs
check f $ g $ h x
check (f . g) x == f (g x)
check a * b + c * d == (a * b) + (c * d)
check x :: y :: zs == x :: (y :: zs)
check a and b or c implies d
check -x * y
check f -1
check not (a < b)

# Glued `.`/`[` vs spaced (D22)
check v.stop == len src
check decimal.scan_json src i
check Some src[i]
check f [i]
check (f x).value
check b"abc"[0] == 'a'
check xs ++ [1, 2] ++ []
check (1, "two", c'3')
check ()
