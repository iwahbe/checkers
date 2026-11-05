module fork_join

fn f sched xs
    let (a, b, c) = par (g xs, h xs, k xs)
    let pair = map2 combine (par (one, two))
    p <- fork using sched
        1
    _ <- fork using sched
        2
    q <- join x = p using sched
        x + 1
    r <- join x = p, y = q using sched
        let z = x + y
        z
    let s = join "," (fork_names xs)
    r
