# A cown can't hold a resource (D156 k): its handle can be shared, so
# nothing would make sure what it holds is closed. Neither can an actor's
# state, which is a cown's. A resource stays with one owner.
module cown_resource

import std.files (File)
import std.cown (Cown, Sched)
import std.actor (Actor)

fn direct f s -> c : f~File, s~Sched, c~Cown File
    cown.new f s

record Job
    out~File
    lines~Nat

fn inside f s -> c : f~File, s~Sched, c~Cown Job
    cown.new (Job f 0) s

fn generic v s -> c : v~own a, s~Sched, c~Cown a
    cown.new v s

fn state f s -> a : f~File, s~Sched, a~Actor (Option File)
    actor.new (Some f) s

# Plain state is fine; the resource is used by its one owner.
fn counts f s -> c : f~File, s~Sched, c~Cown Nat
    files.close f
    cown.new 0 s
