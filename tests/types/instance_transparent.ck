module instance_transparent

# A `transparent` instance function's body is visible to importers; an
# exported function it calls stays sealed.

import class_home.sealed (Size, Open, Calls, one)

fn by_body o -> r : o~Open, r~Bool, r
    Size.size o == 1

fn through_exported c -> r : c~Calls, r~Bool, r
    Size.size c == 1

fn as_called c -> r : c~Calls, r~Bool, r
    Size.size c == one c.v
