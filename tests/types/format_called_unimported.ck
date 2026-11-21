module format_called_unimported

# `format x` where `format` isn't imported: an unknown name, with the
# ways to show `x` and the import they need.

fn called n -> s : n~Int, s~String
    format n
