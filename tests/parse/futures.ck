module futures

fn f sched xs
    let (a, b, c) = par (g xs, h xs, k xs)
    let pair = map2 combine (par (one, two))
    let p = future.fork sched $ \_ ->
        1
    let q = future.join p + 1
    let (x, y) = future.join (p, q)
    let r = future.fork sched $ \_ ->
        let z = x + y
        z
    let s = join "," (fork_names xs)
    r
