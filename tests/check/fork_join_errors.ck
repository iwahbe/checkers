module fork_join_errors

fn single
    par (f x)

fn unbound sched
    fork using sched
        1

fn no_using p
    r <- join x = p
        x
    r

fn fine
    0
