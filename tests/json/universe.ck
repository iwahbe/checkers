# `Type` leads to its declaration in the prelude, with its description (D132).
module universe

enum Box a : a~Type
    Box x : x~a
