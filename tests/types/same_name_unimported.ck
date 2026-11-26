# A type of a module this one doesn't import is shown by its module's name
# when another type of its name is in the message.
module same_name_unimported

import same_name.b
import same_name.c

fn unimported -> r : r~b.T
    c.make
