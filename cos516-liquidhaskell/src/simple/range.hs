{-@ predicate Between Lo N Hi = Lo <= N && N < Hi @-}
{-@ type Range Lo Hi = {v:Int | (Between Lo v Hi)} @-}

{-@ range :: lo:Int -> hi:{v:Int | lo <= v && v < hi} -> [Range lo hi] @-}
range :: Int -> Int -> [Int]
range lo hi
  | lo < hi  = lo : range (lo + 1) hi
  | otherwise = []

{-@ xrange :: hi:{v:Int | 0 <= v && v < hi} -> [Range 0 hi] @-}
xrange = range 0

{-@ measure len :: [a] -> Int @-}
len :: [a] -> Int
len [] = 0
len (x:xs) = 1 + (len xs)

{-@ append' :: xs:[a] -> ys:[a] -> {v:[a] | len v = len xs + len ys} @-}
append' :: [a] -> [a] -> [a]
append' xs [] = xs
append' [] ys = ys
append' (x:xs) ys = x:(append' xs ys)

{-@ map' :: (a -> b) -> xs:[a] -> {v:[b] | len v = len xs} @-}
map' :: (a -> b) -> [a] -> [b]
map' _ [] = []
map' f (x:xs) = (f x):(map' f xs)

{-@ filter' :: (a -> Bool) -> xs:[a] -> {v:[a] | len v <= len xs} @-}
filter' :: (a -> Bool) -> [a] -> [a]
filter' _ [] = []
filter' f (x:xs) = if f x then x:(filter' f xs) else filter' f xs

--- -- ERROR:
--- {-@ measure hasZero :: [Int] -> Prop
---     hasZero []     = false
---     hasZero (x:xs) = x == 0 || (hasZero xs) @-}
--- 
--- {-@ type HasZero = {v : [Int] | (hasZero v)} @-}
--- {-@ xs0 :: HasZero @-}
--- xs0 :: [Int]
--- xs0 = [2, 1, 0, -1, -2]

-- {-@ type Nat = {v:Int | 0 <= v} @-}
-- {-@ class measure sz :: a -> Nat @-}
-- {-@ class Indexable f where
--       size :: xs:_ -> {v:Nat | v = sz xs}
--       at   :: xs:_ -> {v:Nat | v < sz xs} -> a @-}
-- class Indexable f where
--   size :: f a -> Int
--   at   :: f a -> Int -> a
