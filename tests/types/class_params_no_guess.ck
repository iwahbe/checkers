module class_params_no_guess

class Hole s h
    fn hole st x -> r : st~s, x~h, r~s

record Page
    parts~List String

instance Hole Page String
    fn hole p x
        Page (x :: p.parts)

fn known p -> r : p~Page, r~Page
    Hole.hole p "a"

fn never p -> r : p~Page, r~Page
    let f = \x -> Hole.hole p x
    p
