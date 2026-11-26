# A resource type may have instances (D156 i): a class function takes a
# resource exactly once, as any function does.
module resource_instance

import std.files (File)

class Sink a
    fn sink x -> u : x~own a, u~Unit

instance Sink File
    fn sink f
        close f

# Generic code takes a resource only as `own` (D39): so does a class's
# function that generic code passes it to.
fn drain x : x~own a, Sink a
    Sink.sink x

fn closed f : f~File
    drain f

# A class function must take its parameter as `own` to be given at a
# resource type.
class Named a
    fn name x -> s : x~a, s~String

instance Named File
    fn name f
        close f
        "file"

class Pair a
    fn twice x -> p : x~own a, p~(a, a)

# An instance's function is checked as any other: it can't copy a file.
instance Pair File
    fn twice f
        (f, f)

class Forget a
    fn forget x -> u : x~own a, u~Unit

instance Forget File
    fn forget f
        ()

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
