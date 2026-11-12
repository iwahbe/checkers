# Other page

## A table

| Syntax | Meaning |
|---|---|
| `a \| b` | a pipe in code |
| \*not em\* | escaped stars |

## Code

```checkers
module m

# A comment.
fn f x -> y : x~Int, y~Int
    if x > 0 then x else 0 - x

check f (0 - 2) == 2 and "s" ++ "t" == "st"
```

```
plain <code> & text
```
