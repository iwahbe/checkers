# Spaces between tokens (D92).
module spacing
import std.list(map,  reverse)

export abstract record Box +v : v~ Type
    item ~v

fn f x->y:x ~Nat,y~ Int
    let a=x+1*2-(x%3)
    let b =-a
    let c = f(-1)  - g -1
    let d = xs[0]+p.field+list.map(\n->n*2)xs
    let e = [ 1,2 ,3 ]
    let g = (+ 1) . (* 2)
    let System{fs,term} = sys
    if a<=b and not(c==d) then a else b

fn g x : x~Int
    match x
        Num -1->0
        _->x
