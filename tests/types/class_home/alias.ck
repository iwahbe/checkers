module class_home.alias

export class Make t
    fn make u -> r : u~Int, r~t

instance Make Int
    fn make u
        u

export class Build t
    fn build u -> r : u~Int, r~t

instance Build Int
    transparent fn build u
        u
