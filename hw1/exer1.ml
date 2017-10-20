let rec merge ((left: int list), (right: int list)) : (int list) =
    match (left, right) with
    | ([], _) -> right
    | (_, []) -> left
    | (left_head :: left_tail, right_head :: right_tail) ->
            if left_head > right_head then left_head :: merge(left_tail, right)
            else right_head :: merge(left, right_tail)
