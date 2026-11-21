module lambda_applied

# A lambda whose parameters' types are inferred, applied to values that
# aren't variables: the second parameter's type doesn't depend on the first.

fn by_lambda -> r : r~String
    (\a b -> format a ++ format b) 1 "two"
