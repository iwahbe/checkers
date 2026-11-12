# Arrays (D133): each packed width, values at its edges; generic code
# creating arrays of `U8` (packed, so printed as bytes); `set` in place and
# on a shared array; an `Array U8` used as an `Array U32`.
module arrays

import std.system (System, ExitCode)
import std.terminal (Term)
import std.terminal
import std.array

fn show xs term -> r : xs~Array a, term~Term, r~Unit
    terminal.print_line (format (array.to_list xs) ++ " as " ++ format xs) term

# Generic: the element type is a parameter, so its layout comes from the
# caller (D133).
fn twice xs -> r : xs~Array a, r~Array a
    xs ++ array.from_list (array.to_list xs)

fn widen xs -> r : xs~Array U8, r~Array U32
    xs

fn of_u8 xs -> r : xs~List U8, r~Array U8
    array.from_list xs

fn of_i8 xs -> r : xs~List I8, r~Array I8
    array.from_list xs

fn of_u16 xs -> r : xs~List U16, r~Array U16
    array.from_list xs

fn of_u32 xs -> r : xs~List U32, r~Array U32
    array.from_list xs

fn of_i32 xs -> r : xs~List I32, r~Array I32
    array.from_list xs

fn of_u64 xs -> r : xs~List U64, r~Array U64
    array.from_list xs

fn of_i64 xs -> r : xs~List I64, r~Array I64
    array.from_list xs

fn of_int xs -> r : xs~List Int, r~Array Int
    array.from_list xs

# `init` lays its result out for `U8`, written as each element comes.
fn bytes_upto n -> r : n~Nat, r~Bytes
    array.init n (\i -> i % 256)

# `map` into one word per element.
fn negated xs -> r : xs~Array U16, r~Array Int
    array.map (\x -> -x) xs

# A generic function's result laid out for `U8`, from its caller.
fn twos xs -> r : xs~Array I8, r~Array U8
    array.map (\x -> 2) xs

export fn main args sys -> code : args~List String, sys~System, code~ExitCode
    let t = sys.term
    let u8 = of_u8 [0, 1, 255]
    let i8 = of_i8 [-128, -1, 127]
    let u16 = of_u16 [0, 65535]
    let u32 = of_u32 [0, 4294967295]
    let i32 = of_i32 [-2147483648, 2147483647]
    let u64 = of_u64 [0, 18446744073709551615]
    let i64 = of_i64 [-9223372036854775808, 9223372036854775807]
    let bools = array.from_list [True, False]
    let chars = array.from_list [c'a', c'€']
    let words = of_int [-1, 100000000000000000000]
    show u8 t
    show i8 t
    show u16 t
    show u32 t
    show i32 t
    show u64 t
    show i64 t
    show bools t
    show chars t
    show words t
    show (twice u8) t
    show (array.map (\x -> x + 1) i8) t
    show (twos i8) t
    show (bytes_upto 4) t
    # A range's layout (D135 d): `x % 16` is in `0 … 15`, so bytes.
    show (array.map (\x -> x % 16) u32) t
    show (negated u16) t
    let shared = array.from_list [1, 2, 3]
    let changed = array.set shared 0 9
    show shared t
    show changed t
    show (array.set (array.from_list [1, 2, 3]) 2 7) t
    let wide = widen b"ab"
    show (array.set wide 0 300) t
    terminal.print_line (format (wide == array.from_list [97, 98])) t
    terminal.print_line (format (array.reverse b"abc" == b"cba")) t
    terminal.print_line (format (len (array.concat [u8, u8])) ++ " " ++ (if 2 < len u8 then format u8[2] else "?")) t
    Success
