module class_dict_sort_in_function_argument

# A dictionary's constructor at an instance's sort, inside a function
# argument's refinement, needs that sort declared before it is used.
fn shorter r xs -> b : Seq s, r~Option s, xs~s, b~Bool
    match r
        Some rest -> Seq.size rest < Seq.size xs
        None      -> True

fn apply p xs -> r : Seq s, p~(ys~s -> pr~Option s, Seq.size ys <= Seq.size xs, shorter pr ys), xs~s, r~Option s
    p xs

fn none_bytes xs -> r : xs~Bytes, r~Option Bytes, shorter r xs
    None

fn by_bytes xs -> r : xs~Bytes, r~Option Bytes
    apply none_bytes xs

fn none_list xs -> r : xs~List Int, r~Option (List Int), shorter r xs
    None

fn by_list xs -> r : xs~List Int, r~Option (List Int)
    apply none_list xs
