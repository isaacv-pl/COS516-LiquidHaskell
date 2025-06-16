{-@ type ListN a N = {v : [a] | (len v) = N} @-}
{-@ type Pos = {v: Int | v > 0 } @-}

{-@ type Matrix a Rows Cols  = (ListN (ListN a Cols) Rows) @-}

{-@ transpose                :: c:Int -> r:Pos -> Matrix a r c -> Matrix a c r @-}
transpose                    :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose c r ((x:xs) : xss) = (x : map head xss) : transpose (c-1) r (xs : map tail xss)

{-@ xs :: Matrix Int 2 2 @-}
xs :: [[Int]]
xs = [[1, 2], [3, 4]]

{-@ ys :: Matrix Int 2 3 @-}
ys :: [[Int]]
ys = [[1, 2, 3], [4, 5, 6]]

{-@ inv1 ::  [Bool] -> Bool  @-}
inv1 [] = False
inv1 (hd : tl) = if hd then True else inv1 tl

{-@ andy :: [Bool] -> Bool @-}
andy [] = False
andy (hd : tl) = hd && (andy tl)


{-@inv2 :: [Bool] -> Bool @-}
inv2 hd :: tl = if (fold (\ a acc -> acc || (not a)) False (hd :: tl))
  then False else

{-
{-@inv2 :: ListN ListN Bool -> Bool @-}
inv2 [] = True
inv2 ((h1 : h2  t) : tl)  = if (h1 == True && h2 == True) then False  else  inv2 (t : tl)
inv2 ((h : []) : tl) = if h == True then False else inv2 tl
-}
--{-@ type PHP = {a : (ListN (ListN a Cols) Rows) | andy (map inv2 (transpose a)) && andy (map inv1 a)}@-}
