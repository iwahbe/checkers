module effects

fn binds sys
    let System { fs, term = t } = sys
    line <- terminal.read_line t
    (a, b) <- pair_op 1 fs
    _ <- terminal.print_line "done" t
    line

fn behaviours jobs screen sched
    when j = jobs using sched
        j
    when j = jobs, s = screen using sched
        let j2 = add 1 j
        (j2, s)
    0

# Layout is off inside brackets, so a block lambda is bound or passed with `$`.
fn block_lambda xs
    let step = \x ->
        let y = x + 1
        y * 2
    map step xs
