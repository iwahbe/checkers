module template_without_import

# A template in a module that imports neither `std.string` nor the
# classes: only its tag.

import formatters.page (page)

fn by_tag name -> s : name~String, s~String
    page"<p>{name}</p>"

check by_tag "a" == "<p>a</p>"
