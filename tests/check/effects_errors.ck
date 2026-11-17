module effects_errors

fn no_using log sched
    when l = log
        l
    0

# `<-` is not a token: this is `x < -1`.
fn comparison x
    x<-1

fn fine
    1
