module class_type_positivity

# A recursive type can't hold a class's type at itself: what the instance
# gives isn't known when the type is checked.

class Display a
    type Options
    fn display x -> s : x~a, s~String

enum Tree
    Leaf
    Node kids : kids~List (Display.Options Tree)

instance Display Tree
    type Options = Tree -> Int
    fn display t
        "t"
