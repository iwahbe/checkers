module type_arg_record_applied

# Where a type is expected, a record's name applied to types is the type,
# not the record's constructor of the same name.

record Box b
    item~b

fn zero t -> n : t~ghost Type, n~Nat
    0

check zero (Box Int) == 0
check zero (List (Box Int)) == 0
