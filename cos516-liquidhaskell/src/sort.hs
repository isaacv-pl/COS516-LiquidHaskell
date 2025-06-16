{-
-- insertion
insert :: (Ord a) => [a] -> a -> [a]
insert [] y = [y]
insert (x:xs) y
    | y <= x 	= y:(x:xs)
    | otherwise = x:(insert xs y)

insertion :: (Ord a) => [a] -> [a]
insertion [] = []
insertion (x:xs) = insert x (insertion xs)

-- min'
min' :: (Ord a) => [a] -> a
min' [x] = x
min' (x0:x1:xs) = min' ((if x0 <= x1 then x0 else x1):xs)

-- selection
select :: (Ord a) => [a] -> [a] -> (a, [a])
select [x] acc = (x, acc)
select (x0:x1:xs) acc = if x0 <= x1
    then select (x0:xs) (x1:acc)
    else select (x1:xs) (x0:acc)

selection :: (Ord a) => [a] -> [a]
selection [] = []
selection xs = let (y, ys) = select xs [] in y:(selection ys)
-}

-- TODO: invariant on the ordering

-- quicksort
{-@ quicksort :: xs:[a] -> [a] / [len xs, 0] @-}
quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
quicksort (pivot:xs) =
    let lo = quicksort [x | x <- xs, x < pivot]
        hi = quicksort [x | x <- xs, x >= pivot]
    in lo ++ (pivot:hi)

{-
-- mergesort
merge :: (Ord a) => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = if x <= y
    then x:merge xs (y:ys)
    else y:merge (x:xs) ys

mergesort :: (Ord a) => [a] -> [a]
mergesort [] = []
mergesort [x] = [x]
mergesort xs =
    let half = (length xs) `div` 2
        lo = mergesort [x | (x,i) <- zip xs [0..], i < half]
        hi = mergesort [x | (x,i) <- zip xs [0..], i >= half]
    in merge lo hi

-- test
test :: Bool
test =
    let xs = [7, 5, 9, 3, 2, 0, 1, 4, 8] -- Test Case
        as = [0, 1, 2, 3, 4, 5, 7, 8, 9] -- Expected Answer
        is = insertion xs
        ss = selection xs
        qs = quicksort xs
        ms = mergesort xs
    in
    as == is && is == ss && ss == qs && qs == ms
-}
