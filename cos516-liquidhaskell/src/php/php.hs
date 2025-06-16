data List a = Emp               
       	    | (:::) a (List a)  


{-@ type ListN a N = {v: List a | lengthy v == N} @-}

{-@ impossible :: {v:_ | false} -> a @-}
impossible msg = error msg

{-@ measure lengthy @-}
lengthy :: List a -> Int
lengthy Emp = 0
lengthy (_ ::: xs) = 1 + lengthy xs


{-@ inv1 :: List Bool -> Bool  @-}
inv1 Emp = False
inv1 (hd ::: tl) = if hd then True else inv1 tl


data OList a =
      OEmp
    | (:<:) { oHd :: a
            , oTl :: OList a }

{-@ data OList a =
        OEmp
            | (:<:) { oHd :: a
                    , oTl :: OList {v:a | oHd <= v}} @-}

{-@ type ListNE a = {v:List a| 0 < lengthy v} @-}

{-@ mapp :: (a -> b) -> xs:List a -> ListN b (lengthy xs) @-}
mapp _ Emp         = Emp
mapp f (x ::: xs)  = f x ::: mapp f xs

{-@ heady        :: ListNE a -> a @-}
heady (x ::: _)  = x
heady _          = impossible "head"

{-@ taily        :: ListNE a -> List a @-}
taily (_ ::: xs) = xs
taily _          = impossible "tail"

data Hole a = Hole (List Bool)
{-@ type P1 a =  {v : List Bool | inv1 v} @-} 
{-@ data Hole a = Hole (P1 a) @-}

{-@ transpose :: a : List (List Bool) -> ListN@-}
transpose :: List (List Bool) -> List (List Bool)
transpose Emp = Emp
transpose (Emp ::: tls) = transpose tls
transpose ((h ::: t) ::: tls) = 
	(h ::: mapp heady tls) ::: (transpose (t ::: (mapp taily tls)))

foldy :: (a -> b -> b) -> b -> List a -> b
foldy _ acc Emp        = acc
foldy f acc (x ::: xs) = f x (foldy f acc xs)

{-@ foldr1 :: (a -> a -> a) -> ListNE a -> a @-}
foldr1 f (x ::: xs) = foldy f x xs
foldr1 _ _          = impossible "foldr1"

{-
inv2 :: List List Bool -> Bool
inv2 Emp = True
inv2 ((h1 ::: h2 ::: t) ::: tl)  = if (h1 == True && h2 == True) then False  else  inv2 (t ::: tl)
inv2 ((h ::: Emp) ::: tl) = if h == True then False else inv2 tl

data Php a = Php (List (Hole (List Bool)))
{-@ type P2 a = {v : List (Hole (List Bool)) | inv2 (transpose v)} @-}
{-@ data Php a = Php (P2 a) @-}

-}
