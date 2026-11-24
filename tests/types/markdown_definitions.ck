# Link reference definitions: read one after another to the end of the
# text, each at least a byte; what isn't one stays text.
module markdown_definitions

import std.markdown (Definition)
import std.markdown
import std.list

fn labels text -> r : text~String, r~List String
    list.map (\d -> d.label) (markdown.parse text).definitions

check labels "" == []
check markdown.to_html (markdown.parse "") == ""
check labels "[a]: /u" == ["a"]
check labels "[a]: /u\n[b]: /v \"t\"\n[a]: /w\n" == ["a", "b", "a"]
check markdown.to_html (markdown.parse "[a]: /u\n[b]: /v \"t\"\n[a] [b]") == "<p><a href=\"/u\">a</a> <a href=\"/v\" title=\"t\">b</a></p>\n"
check labels "[a]:" == []
check markdown.to_html (markdown.parse "[a]:") == "<p>[a]:</p>\n"
check labels "[]: /u" == []
check labels "[a]: /u \"t\" x" == []
check labels "[a]: /u\n\"t\" x" == ["a"]
check markdown.to_html (markdown.parse "[a]: /u\n\"t\" x") == "<p>&quot;t&quot; x</p>\n"
check labels "[a]: /u\nb\n=" == ["a"]
check markdown.to_html (markdown.parse "[a]: /u\nb\n=") == "<h1>b</h1>\n"
