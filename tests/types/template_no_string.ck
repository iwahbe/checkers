module template_no_string

# A template in a program that loads `std.string` nowhere else: its tag's
# result has no `Template` instance.

fn count n k -> c : n~Nat, k~Nat, c~Int
    k

fn by_count -> c : c~Int
    count"text"
