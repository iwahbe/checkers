module when_last

fn bump c sched : c~Cown Nat, sched~Sched
    when v = c using sched
        v + 1
