module string_utils.string

export fn twice s -> t : s~String, t~String
    s ++ s
