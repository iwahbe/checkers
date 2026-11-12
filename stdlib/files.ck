# files.ck — the file system. `Fs` is an authority (copied on use); an open
# `File` is a resource (used exactly once, closed explicitly). SPEC §8.3–8.4.
# Everything that is a file is a `File` (D112): an open file, a child's pipe
# (`std.proc`), and the standard streams (`std.terminal`).
module std.files

# The authority to use the file system (copied on use); part of `System`.
# `within` confines one to a directory.
export abstract enum Fs
# An open file: a resource, used exactly once and closed with `close`.
# Functions that use a `File` give it back for the next use.
export abstract enum File
# Why a file operation failed; `describe` says it in words.
export abstract enum IoError

# The contents of the file at `path`.
export fn read path fs -> r : path~String, fs~Fs, r~Result Bytes IoError
    __builtin

# Write `contents` to the file at `path`, creating it or replacing what
# it held.
export fn write path contents fs -> r : path~String, contents~Bytes, fs~Fs, r~Result Unit IoError
    __builtin

# An `Fs` that reaches only `dir` and what is inside it: its paths are
# relative to `dir`, and an absolute path or one with `..` fails.
export fn within dir fs -> r : dir~String, fs~Fs, r~Fs
    __builtin

# The error in words, as the operating system gives it.
export fn describe e -> s : e~IoError, s~String
    __builtin

# Open the file at `path` for reading.
export fn open path fs -> r : path~String, fs~Fs, r~Result File IoError
    __builtin

# Open the file at `path` for writing, creating it or emptying it.
export fn create path fs -> r : path~String, fs~Fs, r~Result File IoError
    __builtin

# Close the file, writing out what is buffered.
export fn close f -> r : f~File, r~Unit
    __builtin

# The next line, without its `\n` (invalid UTF-8 becomes U+FFFD); `None` at
# the end.
export fn read_line f -> r : f~File, r~(Option String, File)
    __builtin

# Write `s` and a newline. Write errors other than misuse are ignored;
# `write_bytes` reports them.
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

# Write `b`.
export fn write_bytes b f -> r : b~Bytes, f~File, r~(Result Unit IoError, File)
    __builtin

# Write out what is buffered now, rather than when the program next waits
# or ends (§13.8): for a reply another program is waiting for.
export fn flush f -> r : f~File, r~(Result Unit IoError, File)
    __builtin

# Create the directory `dir` and any of its parents that are missing; a
# directory that already exists is fine.
export fn create_dirs dir fs -> r : dir~String, fs~Fs, r~Result Unit IoError
    __builtin

# An entry of a directory: its name and whether it is a directory.
export record Entry
    name~String
    dir~Bool

# The entries of a directory, sorted by name, without `.` and `..`.
export fn list dir fs -> r : dir~String, fs~Fs, r~Result (List Entry) IoError
    __builtin
