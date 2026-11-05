module Bad_Module

enum json_value
    null_value
    Number n : n~Int

record httpServer
    PortNumber~Nat

type small_nat = N~Nat, N < 10

let maxDepth = 512
let Pi = 3

fn parseHTTPRequest Input -> Result : Input~Bytes
    let lineCount = 0
    match Input
        Some FirstByte -> FirstByte
        _ -> lineCount

fn _private_helper _unused
    _unused
