------------------------------------------------------------------------
-- BEGIN list.hs
------------------------------------------------------------------------

data List a = Nil | Cons a (List a) deriving (Show)
infixr 5 `Cons`

{-@ list1 :: List Nat @-}
list1 :: List Int
list1 = 1 `Cons` 2 `Cons` 3 `Cons` Nil

{-@ measure llength @-}
llength :: List a -> Int
llength Nil           = 0
llength (x `Cons` xs) = 1 + llength xs

{-@ Nil   ::  { ys : List a | len ys == 0 } @-}
{-@ Cons  ::  a -> xs : List a -> { ys : List a | len ys == 1 + len xs } @-}

{-@ lmap :: (a -> b) -> xs : List a -> { ys : List b | len xs == len ys } / [ len xs ] @-}
lmap :: (a -> b) -> List a -> List b
lmap _ Nil           = Nil
lmap f (x `Cons` xs) = f x `Cons` lmap f xs

{-@ lfilter :: (a -> Bool) -> xs:List a -> {ys:List a | llength ys <= llength xs} / [llength xs] @-}
lfilter :: (a -> Bool) -> List a -> List a
lfilter _ Nil = Nil
lfilter f (x `Cons` xs)
  | f x = x `Cons` lfilter f xs
  | otherwise = lfilter f xs

{-@ lappend :: xs:List a -> ys:List a -> {v:List a | llength v == llength xs + llength ys} / [llength xs] @-}
lappend :: List a -> List a -> List a
lappend xs Nil = xs
lappend Nil ys = ys
lappend (x `Cons` xs) ys = x `Cons` lappend xs ys

{-@ impossible :: {v : _ | false} -> a @-}
impossible msg = error msg

{-@ lhead :: {v:List a | llength v > 0} -> a @-}
lhead (x `Cons` _)  = x
lhead _ = impossible "lhead"

{-@ ltail :: {v:List a | llength v > 0} -> List a @-}
ltail (_ `Cons` xs) = xs
ltail _ = impossible "tail"

{-@ lfoldr :: (a -> b -> b) -> b -> List a -> b @-}
lfoldr :: (a -> b -> b) -> b -> List a -> b
lfoldr f acc Nil = acc
lfoldr f acc (x `Cons` xs) = f x (lfoldr f acc xs)

{-@ lfoldl :: (b -> a -> b) -> b -> List a -> b @-}
lfoldl :: (b -> a -> b) -> b -> List a -> b
lfoldl f acc Nil = acc
lfoldl f acc (x `Cons` xs) = lfoldl f (f acc x) xs

{-@ predicate NonNil X = (llength X > 0) @-}

------------------------------------------------------------------------
--- END list.hs
------------------------------------------------------------------------

------------------------------------------------------------------------
-- transpose
------------------------------------------------------------------------

{-@ type Pos = {v: Int | v > 0 } @-}
{-@ type Nat = {v: Int | v >= 0 } @-}
{-@ type ListN a N = {v : List a | (llength v) = N} @-}
{-@ type Matrix a Rows Cols  = (ListN (ListN a Cols) Rows) @-}
{-@ transpose                :: c:Nat -> r:Pos -> Matrix a r c -> Matrix a c r @-}
transpose                    :: Int -> Int -> List (List a) -> List (List a)
transpose 0 _ _              = Nil
transpose c r (Cons (Cons x xs) xss) = (x `Cons` lmap (\(Cons y ys) -> y) xss) `Cons` transpose (c-1) r (xs `Cons` lmap (\(Cons y ys) -> ys) xss)

------------------------------------------------------------------------
-- transpose example
------------------------------------------------------------------------

{-@ xs :: Matrix Int 2 2 @-}
xs :: List (List Int)
xs = Cons (Cons 1 (Cons 2 Nil)) (Cons (Cons 3 (Cons 4 Nil)) Nil)
{-@ xst :: Matrix Int 2 2 @-}
xst :: List (List Int)
xst = transpose (llength (lhead xs)) (llength xs) xs

{-@ ys :: Matrix Int 2 3 @-}
ys :: List (List Int)
ys = Cons (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons (Cons 4 (Cons 5 (Cons 6 Nil))) Nil)
{-@ yst :: Matrix Int 3 2 @-}
yst :: List (List Int)
yst = transpose (llength (lhead ys)) (llength ys) ys

------------------------------------------------------------------------
-- Pigeon Hole Principle
------------------------------------------------------------------------

{-@ measure anyTrue @-}
anyTrue :: List Bool -> Bool
anyTrue Nil = False
anyTrue (x `Cons` xs) = x || anyTrue xs

{-@ measure isEveryPigeonInAHole @-}
isEveryPigeonInAHole ::  List (List Bool) -> Bool
isEveryPigeonInAHole Nil = True
isEveryPigeonInAHole (x `Cons` xs) = anyTrue x && isEveryPigeonInAHole xs

{-@ measure allFalse @-}
allFalse :: List Bool -> Bool
allFalse Nil = True
allFalse (x `Cons` xs) = not x && allFalse xs

{-@ measure atMostOneTrue @-}
atMostOneTrue :: List Bool -> Bool
atMostOneTrue Nil = True
atMostOneTrue (x `Cons` xs) = (not x || allFalse xs) && atMostOneTrue xs

{-@ measure isOnePigeonPerHole @-}
isOnePigeonPerHole ::  List (List Bool) -> Bool
isOnePigeonPerHole Nil = True
isOnePigeonPerHole (x `Cons` xs) = atMostOneTrue x && isOnePigeonPerHole xs

{-
{-@isOnePigeonPerHoleT P H :: Matrix Bool P H @-}
isOnePigeonPerHoleT ::  List (List Bool) -> Bool
isOnePigeonPerHoleT xs = isOnePigeonPerHole(transpose xs)
-}

{-@ type PHP P H = {v : Matrix Bool P H | isEveryPigeonInAHole v} @-}

------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------

{-@ type TRUE = {v:Bool | v } @-}
{-@ type FALSE = {v:Bool | not v } @-}

{-@ test_anyTrue_Nil :: FALSE @-}
test_anyTrue_Nil :: Bool
test_anyTrue_Nil = anyTrue Nil
{-@ test_anyTrue_FTF :: TRUE @-}
test_anyTrue_FTF :: Bool
test_anyTrue_FTF = anyTrue (False `Cons` True `Cons` False `Cons` Nil)
{-@ test_anyTrue_FFF :: FALSE @-}
test_anyTrue_FFF :: Bool
test_anyTrue_FFF = anyTrue (False `Cons` False `Cons` False `Cons` Nil)

{-@ test_allFalse_Nil :: TRUE @-}
test_allFalse_Nil :: Bool
test_allFalse_Nil = allFalse Nil
{-@ test_allFalse_FTF :: FALSE @-}
test_allFalse_FTF :: Bool
test_allFalse_FTF = allFalse (False `Cons` True `Cons` False `Cons` Nil)
{-@ test_allFalse_FFF :: TRUE @-}
test_allFalse_FFF :: Bool
test_allFalse_FFF = allFalse (False `Cons` False `Cons` False `Cons` Nil)

{-@ test_atMostOneTrue_Nil :: TRUE @-}
test_atMostOneTrue_Nil :: Bool
test_atMostOneTrue_Nil = atMostOneTrue Nil
{-@ test_atMostOneTrue_FTF :: TRUE @-}
test_atMostOneTrue_FTF :: Bool
test_atMostOneTrue_FTF = atMostOneTrue (False `Cons` True `Cons` False `Cons` Nil)
{-@ test_atMostOneTrue_FFF :: TRUE @-}
test_atMostOneTrue_FFF :: Bool
test_atMostOneTrue_FFF = atMostOneTrue (False `Cons` False `Cons` False `Cons` Nil)
{-@ test_atMostOneTrue_TFT :: FALSE @-}
test_atMostOneTrue_TFT :: Bool
test_atMostOneTrue_TFT = atMostOneTrue (True `Cons` False `Cons` True `Cons` Nil)

{-@ test_php_0_0 :: PHP 0 0 @-}
test_php_0_0 :: List (List Bool)
test_php_0_0 = Nil

{-@ test_php_1_1 :: PHP 1 1 @-}
test_php_1_1 :: List (List Bool)
test_php_1_1 = Cons (Cons True Nil) Nil

{-@ test_php_2_2 :: PHP 2 2 @-}
test_php_2_2 :: List (List Bool)
test_php_2_2 = Cons (Cons True (Cons False Nil)) (Cons (Cons False (Cons True Nil)) Nil)
