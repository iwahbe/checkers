module defaults.source

export record Box a
    item~a

export class Wrapped a
    type Value = Box a
    fn wrap x -> y : x~a, y~Value
