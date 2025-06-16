--***********************PRELIMINARY STUFF ***************************
{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size []     = 0
size (_:rs) = 1 + size rs
{- Measure translates the above to the following:
data [a] where
  []  :: {v: [a] | size v = 0}
  (:) :: a -> xs:[a] -> {v:[a]|size v = 1 + size xs}
-}

type List a = [a]
{-@ type ListN a N = {v:List a | size v = N} @-}

--***********************Vector Definitions ***************************
{-@ data Vector a = V { vDim  :: Nat
                      , vElts :: ListN a vDim }
@-}
data Vector a = V { vDim :: Int
                  , vElts :: [a]
                  }
                deriving (Eq)
{-@ vDim :: x:_ -> {v: Nat | v = vDim x} @-}

{-@ vEmp :: VectorN a 0 @-}
vEmp = V 0 []

{-@ vCons :: a -> x:Vector a -> VectorN a {vDim x + 1} @-}
vCons x (V n xs) = V (n+1) (x:xs)

-- | Non Empty Vectors
{-@ type VectorNE a  = {v:Vector a | vDim v > 0} @-}

-- | Vectors of size N
{-@ type VectorN a N = {v:Vector a | vDim v = N} @-}

-- | Vectors of Size Equal to Another Vector X
{-@ type VectorX a X = VectorN a {vDim X}        @-}

{-@ vHd :: VectorNE a -> a @-}
vHd (V _ (x:_))  = x
vHd _            = die "nope"

{-@ vTl          :: x:VectorNE a -> VectorN a {vDim x - 1} @-}
vTl (V n (_:xs)) = V (n-1) xs
vTl _            = die "nope"

{-@ for        :: x:Vector a -> (a -> b) -> VectorX b x @-}
for (V n xs) f = V n (map f xs)

{-@ vBin :: (a -> b -> c) -> x:Vector a
                          -> VectorX b x
                          -> VectorX c x
  @-}
vBin op (V n xs) (V _ ys) = V n (zipWith op xs ys)

{-@ dotProduct :: (Num a) => x:Vector a -> VectorX a x -> a @-}
dotProduct x y = sum $ vElts $ vBin (*) x y

vecFromList     :: [a] -> Vector a
vecFromList [] = vEmp
vecFromList (x:xs) = vCons x (vecFromList xs)

test6  = dotProduct vx vy    -- should be accepted by LH
  where
    vx = vecFromList [1,2,3]
    vy = vecFromList [4,5,6]

--***********************Matrix Definitions ***************************
{-@ type Pos = {v:Int | 0 < v} @-}
{-@ data Matrix a =
      M { mRow  :: Pos
        , mCol  :: Pos
        , mElts :: VectorN (VectorN a mCol) mRow
        }
  @-}
data Matrix a = M { mRow  :: Int
                  , mCol  :: Int
                  , mElts :: Vector (Vector a)
                  }
              deriving (Eq)
{-@ type MatrixN a R C   = {v:Matrix a | Dims v R C } @-}
{-@ predicate Dims M R C = mRow M = R && mCol M = C   @-}


{-@ transpose :: m:Matrix a -> MatrixN a (mCol m) (mRow m) @-}
transpose (M r c rows) = M c r $ txgo c r rows

{-@ txgo      :: c:Nat -> r:Nat
              -> VectorN (VectorN a c) r
              -> VectorN (VectorN a r) c
  @-}
txgo c r rows = undefined

--***********************PHP Definitions ***************************
{-@ inv1 :: Vector Bool -> Bool  @-}
inv1 [] = False
inv1 (hd : tl) = if hd then True else inv1 tl



--***********************Misc. Definitions ***************************
  {-
{-@ measure notEmpty @-}
notEmpty       :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True

{-We now have two refinements for the list constructors giving us the following:
data [a] where
  []  :: {v: [a] | not (notEmpty v) && size v = 0}
  (:) :: a
      -> xs:[a]
      -> {v:[a]| notEmpty v && size v = 1 + size xs}
-}

-- Alias for unrefined list

{-@ type ListX a X = ListN a {size X}        @-}
{-@ type ListXY a X Y = ListN a {size X + size Y}        @-}

{-@ map      :: (a -> b) -> xs:List a -> ListX b xs @-}
map _ []     = []
map f (x:xs) = f x : map f xs

{-
range :: lo:Int -> hi:{Int | lo <= hi}
-> [(Rng lo hi)]
type Rng Lo Hi = {v:Int | (Btwn Lo v Hi)} -}

{-@ predicate Tinier X Y Z = Min (size X) (size Y) (size Z) @-}
{-@ predicate Min X Y Z = (if Y < Z then X = Y else X = Z)  @-}

{-@ zip :: as:[a] -> bs:[b] -> {v:[(a,b)] | Tinier v as bs} @-}
zip (a:as) (b:bs) = (a, b) : zip as bs
zip [] _          = []
zip _  []         = []

{-@ reverse       :: xs:List a -> ListX a xs @-}
{-@ go :: acc:List a -> xs:List a -> ListXY a acc xs @-}
--{-@ go :: acc:List a -> xs:List a -> ListN a {(size acc) + (size xs)} @-}
reverse :: List a -> List a
reverse xs        = go [] xs
  where
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs

{-@ prop_map :: List a -> TRUE @-}
prop_map xs = size ys == size xs
  where
    ys      = map id xs

{-@take :: n:Nat -> xs:List a -> {v:List a | Min (size v) n (size xs)}@-}
take 0 _       = []
take _ []      = []
take n (x:xs)  = x : take (n-1) xs

{-@ test5 :: [ListN String 2] @-}
test5 = [ take 2  ["cat", "dog", "mouse"]
        , take 20 ["cow", "goat"]        ]
-}
