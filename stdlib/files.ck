# files.ck — the file system. `Fs` is an authority (copied on use); an open
# `File` is a resource (used exactly once, closed explicitly). SPEC §8.3–8.4.
# Everything that is a file is a `File` (D112): an open file, a child's pipe
# (`std.proc`), and the standard streams (`std.terminal`).
module std.files

export abstract enum Fs
export abstract enum File
export abstract enum IoError

export fn read path fs -> r : path~String, fs~Fs, r~Result Bytes IoError
    __builtin

export fn write path contents fs -> r : path~String, contents~Bytes, fs~Fs, r~Result Unit IoError
    __builtin

export fn within dir fs -> r : dir~String, fs~Fs, r~Fs
    __builtin

export fn describe e -> s : e~IoError, s~String
    __builtin

export fn open path fs -> r : path~String, fs~Fs, r~Result File IoError
    __builtin

export fn create path fs -> r : path~String, fs~Fs, r~Result File IoError
    __builtin

export fn close f -> r : f~File, r~Unit
    __builtin

# The next line, without its `\n` (invalid UTF-8 becomes U+FFFD); `None` at
# the end.
export fn read_line f -> r : f~File, r~(Option String, File)
    __builtin

export fn write_line s f -> r : s~String, f~File, r~(Unit, File)
    __builtin

# At most `n` bytes, waiting until at least one is there: empty only at the
# end of the file (or when `n` is 0).
export fn read_some n f -> r : n~Nat, f~File, r~(Result Bytes IoError, File)
    __builtin

# `n` bytes, or fewer only if the file ends first.
export fn read_exactly n f -> r : n~Nat, f~File, r~(Result Bytes IoError, File)
    __builtin

# Everything up to the end of the file.
export fn read_rest f -> r : f~File, r~(Result Bytes IoError, File)
    __builtin

export fn write_bytes b f -> r : b~Bytes, f~File, r~(Result Unit IoError, File)
    __builtin

# An entry of a directory.
export record Entry
    name~String
    dir~Bool

# The entries of a directory, sorted by name, without `.` and `..`.
export fn list dir fs -> r : dir~String, fs~Fs, r~Result (List Entry) IoError
    __builtin
