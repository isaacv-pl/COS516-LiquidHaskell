{-@ type TRUE = {v : Bool | v} @-}
{-@deMorgan :: Bool -> Bool -> TRUE @-}
deMorgan :: Bool -> Bool -> Bool
deMorgan x1 x2 = not (x1 && x2) == not x1 || not x2
