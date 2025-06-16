{-@ type Pos = {v:Int | 0 < v} @-}
{-@ safeDiv :: Int -> Pos -> Int   @-}
safeDiv :: Int -> Int -> Int 
safeDiv _ 0 = error "NEVER"
safeDiv x n = x `div` n
right = safeDiv 9 3
wrong = safeDiv 9 0
