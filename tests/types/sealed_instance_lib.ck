module sealed_instance_lib

# An instance's function, which every importer sees, calls a function this
# module exports.

import std.string (Display)

export record Meters
    value~Int

# Exported, so sealed: importers know only its signature.
export fn sign m -> s : m~Meters, s~String
    if m.value < 0 then "-" else "+"

instance Display Meters
    fn display m os
        sign m
