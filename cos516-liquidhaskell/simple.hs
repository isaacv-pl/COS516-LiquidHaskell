ltranspose :: [[Int]] -> [[Int]]
ltranspose [] = []
ltranspose (xs) = (map (head) xs) : ltranspose (map (tail) xs)
