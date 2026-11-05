# files.ck — the file system. `Fs` is an authority (copied on use); an open
# `File` is a resource (used exactly once, closed explicitly). SPEC §8.3–8.4.
module files

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

export fn read_line f -> r : f~File, r~(Option String, File)
    __builtin

export fn write_line s f -> r : s~String, f~File, r~(Unit, File)
    __builtin
