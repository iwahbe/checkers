module class_home.refined

export class Size a
    fn size x -> n : x~a, n~Int

instance Size Bool
    fn size b -> n : b~Bool, n~Int, n >= 0
        if b then 1 else 0
