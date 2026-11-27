module oneshot_field

# A closure that uses a resource is a resource, of type `own (Unit -> Unit)`.
# A record field of a function type that may be called any number of times
# can't hold one; a field declared `own (Unit -> Unit)` can, and then the
# record holds a resource: reading another of its fields would drop it.

import std.files (File)
import std.files

record Job
    run~Unit -> Unit
    n~Int

fn into_field file -> r : file~File, r~Int
    let job = Job (\_ -> close file) 3
    job.n

record Once
    run~own (Unit -> Unit)
    n~Int

fn read_other file -> r : file~File, r~Int
    let job = Once (\_ -> close file) 3
    job.n

# Taken apart, each field used: no error.
fn taken_apart file -> r : file~File, r~Int
    match Once (\_ -> close file) 3
        Once run n ->
            run ()
            n

# Close `f`, whatever closing gives.
fn close f : f~File
    let _ = files.close f
    ()
