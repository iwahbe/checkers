module one_field

# A value computed at compile time is read back by its type: one of a type
# stored as its one field is its constructor applied, and a `match` on it
# picks its arm when the program is staged.

record Meters
    m~Int

fn scaled k x -> y : k~comptime Int, x~Int, y~Int
    match Meters (k * 2)
        Meters n -> n * x

fn doubled x -> y : x~Int, y~Int
    scaled 3 x

fn far k -> d : k~comptime Int, d~Meters
    Meters (k + 1)

fn reached x -> d : x~Int, d~Meters
    let d = far 9
    Meters (d.m + x)

fn origin x -> d : x~Int, d~(Meters, Int)
    (far 0, x)

check doubled 2 == 12 and reached 1 == Meters 11 and origin 4 == (Meters 1, 4)
