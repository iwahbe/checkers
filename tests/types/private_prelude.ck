# A name the prelude declares but doesn't export, used bare: every module
# imports the prelude, so the error says the name is private to it.
module private_prelude

fn by_name x y -> r : x~String, y~String, r~Bool
    string_le x y
