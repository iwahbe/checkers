module block_in_brackets

# Inside brackets lines continue, so no block can start there.

fn by_match a b
    a
        and (match b
            Some _ -> True
            None   -> False)

fn in_list b
    [match b
        Some _ -> 1
        None   -> 0]

fn by_if a b
    a
        and (if b
            False
        else
            True)

fn one_line_if a b
    a and (if b then False else True)

fn by_let xs
    map (\x ->
            let y = x + 1
            y) xs

fn by_when j sched
    f (when x = j using sched
        x)

fn in_index xs b
    xs[match b
        _ -> 0]

fn after
    1
