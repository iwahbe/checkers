# Templates stay glued to their tags; holes are kept as written.
module templates

fn f name n
    let a = format"{name}  is {n+1}"
    let b = page"<p>{f "a}" (g [1,2])}</p>" x
    let c = format"{{ {inner"{x}"} }}"
    let d = format "{x}"
    show   format"{| Hex}"   y
