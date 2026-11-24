# An instance of another module's class, used from a third module.
module class_home.mark

import class_home.pinned (Make)

export record Mark
    on~Bool

instance Make Mark
    fn make n a
        Mark (n > 0)
