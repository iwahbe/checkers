# A future of a resource is a resource (D156 l): it must be joined exactly
# once, so a resource made in a behaviour can't be dropped with its future.
module future_resource

import std.files (Fs, File, IoError)
import std.cown (Cown, Sched)
import std.future (Future)

fn done r : r~Result File IoError
    match r
        Ok f  -> files.close f
        Err _ -> ()

partial fn never fs sched : fs~Fs, sched~Sched
    let a = future.fork sched $ \_ ->
        files.open "a.txt" fs
    ()

partial fn dropped fs sched : fs~Fs, sched~Sched
    let _ = future.fork sched $ \_ ->
        files.open "a.txt" fs
    ()

partial fn twice fs sched : fs~Fs, sched~Sched
    let a = future.fork sched $ \_ ->
        files.open "a.txt" fs
    let _ = future.join a sched $ \r ->
        done r
    let _ = future.join a sched $ \r ->
        done r
    ()

fn in_cown f s -> c : f~Future File, s~Sched, c~Cown (Future File)
    cown.new f s

# Joined once: fine. A future of plain values may be dropped.
partial fn once fs sched : fs~Fs, sched~Sched
    let a = future.fork sched $ \_ ->
        files.open "a.txt" fs
    let _ = future.join a sched $ \r ->
        done r
    let _ = future.fork sched $ \_ ->
        1 + 1
    ()
