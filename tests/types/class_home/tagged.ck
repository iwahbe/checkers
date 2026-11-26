# A class whose type's default uses its parameter and a type of this
# module: an instance elsewhere takes it as written here.
module class_home.tagged

export class Tagged a
    type Entry = (a, Tag)
    fn tag_of x -> e : x~a, e~Entry

export record Tag
    n~Int
