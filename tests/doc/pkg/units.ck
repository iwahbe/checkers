# units.ck — units of measure.
module pkg.units

# One. A block may import this package's modules, as this module does; its
# `#!` lines are left out of the page, the Markdown one too:
#
#     #! import pkg.units (UNIT)
#     check UNIT == 1
#
# It needn't: a module's blocks import it (D164).
#
#     check UNIT + UNIT == 2
#
# ```
# #! import pkg.units (UNIT)
# ```
export let UNIT = 1
