module instance_qualified

# An instance of a class named through its module's qualifier, with a
# context named the same way.
instance order.Ord (List a) : order.Ord a
    fn le xs ys
        True
