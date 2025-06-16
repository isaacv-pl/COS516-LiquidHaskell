{-@ measure len :: [a] -> Int @-}
len :: [a] -> Int
len [] = 0
len (x:xs) = 1 + (len xs)


{-@ type ListN a N = {v : [a] | (len v) = N} @-}
{-@ type Pos = {v: Int | v > 0 } @-}

{-@ type Matrix a Rows Cols  = (ListN (ListN a Cols) Rows) @-}

{-@ measure transpose@-}
{-@ transpose                :: c:Int -> r:Pos -> Matrix a r c -> Matrix a c r @-}
transpose                    :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose c r ((x:xs) : xss) = (x : map head xss) : transpose (c-1) r (xs : map tail xss)

{-@ measure anyTrue @-}
anyTrue :: [Bool] -> Bool
anyTrue [] = False
anyTrue ( x:xs) = x || anyTrue xs

{-@ measure isEveryPigeonInAHole @-}
isEveryPigeonInAHole ::  [[Bool]] -> Bool
isEveryPigeonInAHole [] = True
isEveryPigeonInAHole ( x:xs) = anyTrue x && isEveryPigeonInAHole xs

{-@ measure allFalse @-}
allFalse ::  [Bool] -> Bool
allFalse [] = True
allFalse ( x:xs) = not x && allFalse xs

{-@ measure atMostOneTrue @-}
atMostOneTrue :: [Bool]-> Bool
atMostOneTrue [] = True
atMostOneTrue ( x:xs) = (not x || allFalse xs) && atMostOneTrue xs

{-@ measure isOnePigeonPerHole @-}
isOnePigeonPerHole ::  [[Bool]] -> Bool
isOnePigeonPerHole [] = True
isOnePigeonPerHole ( x:xs) = atMostOneTrue x && isOnePigeonPerHole xs




{-@ zs :: PHP 3 3 @-}
zs :: [[Bool]]
zs = [[False, False, True], [True, False, False], [False, True, False]]

{-
{-@all2 :: Int -> Pos -> [[Bool]] -> Bool @-}
all2 ::  Int -> Int -> [[Bool]] -> Bool
all2 p h l = andy (map inv2 (transpose h p l))
-}
{-
{-@ type PHP P H = {v : Matrix Bool P H | (all2 v P H) && andy (map inv1 v)} @-}

{-@ zs :: PHP 3 3 @-}
zs :: [[Bool]]
zs = [[False, False, True], [True, False, False], [False, True, False]]
-}
