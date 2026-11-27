module lib.known

export fn next x -> r : x~Int, x >= 1, r~Int
    x + 1

# Known once this module is proved: computed by running `next`.
export let SEVEN = next 6
