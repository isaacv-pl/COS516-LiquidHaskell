{-@ inv1 :: [bool] -> bool  @-}
inv1 [] = false
inv1 (hd : tl) = if hd then true else inv1 tl

{-
data hole a = hole [bool]
{-@ type p1 = {v :  [bool] | inv1 v} @-}
{-@ data hole = hole (p1) @-}
-}

{-@ lengthr :: [[a]] -> nat @-}
lengthr :: [[a]] -> int
lengthr [] = 0
lengthr (h : tl) = 1 + lengthr tl
{-
{-@ measure lengthc @-}
{-@ lengthc :: [[a]] -> nat @-}
lengthc :: [[a]] -> int
lengthc [] = 0
lengthc (h : _) = length h

{-@ type listn a n = {v : [a] | length v == n} @-}

{-@ type listrc a r c = {v : [[a]] | lengthr v == r && lengthc v == c} @-}

{-@ transpose :: (xs : [[bool]]) -> listrc bool (lengthc xs) (lengthr xs) @-}
transpose :: [[bool]] -> [[bool]]
transpose [] = []
transpose ([] : tls) = transpose tls
transpose ((h : t) : tls) =
      (h : map head tls) : (transpose (t : (map tail tls)))
-}
