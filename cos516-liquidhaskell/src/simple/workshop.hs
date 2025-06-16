-- http://ucsd-progsys.github.io/lh-workshop/02-refinements.html

{-@ type Zero = {v:Int | v = 0} @-}
{-@ zero :: Zero @-}
zero :: Int
zero =  0

{-@ type Nat = {v:Int | 0 <= v} @-}
{-@ nats :: [Nat]               @-}
nats :: [Int]
nats = [0, 1, 2, 3]

{-@ type Pos = {v:Int | 0 < v} @-}
{-@ poss :: [Pos]              @-}
poss :: [Int]
poss =  [1, 2, 3]

-- BEGIN NOTE
-- Using lowercase q instead of Q would produce this error:
-- -- Error: Malformed application of type alias `ZNum`
-- --    | {-@ num3 :: ZNum 3 @-}
-- --                   ^
-- -- Expects 1 type arguments before expression arguments
-- END NOTE
{-@ type ZNum Q = {v:Int | v = Q} @-}
{-@ num3 :: ZNum 3 @-}
num3 :: Int
num3 = 3

{-@ impossible :: {v:_ | false} -> a @-}
impossible msg = error msg

{-@ safeDiv :: Int -> Pos -> Int   @-}
safeDiv :: Int -> Int -> Int
safeDiv _ 0 = impossible "divide-by-zero"
safeDiv x n = x `div` n

calc :: IO ()
calc = do
    putStrLn "Enter numerator"
    n <- readLn
    putStrLn "Enter denominator"
    d <- readLn
    putStrLn ("Result = " ++ (if d <= 0 then "NAN" else show (safeDiv n d)))

{-@ size :: [a] -> Pos @-}
size :: [a] -> Int
size [] = 0
size [x] = 1
size (x:xs) = 1 + size xs
