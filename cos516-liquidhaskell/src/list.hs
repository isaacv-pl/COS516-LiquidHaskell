data List a = Nil | Cons a (List a) deriving (Show)
infixr 5 `Cons`

{-@ list1 :: List Nat @-}
list1 :: List Int
list1 = 1 `Cons` 2 `Cons` 3 `Cons` Nil

{-@ data List [llength] @-}
{-@ measure llength @-}
llength :: List a -> Int
llength Nil           = 0
llength (x `Cons` xs) = 1 + llength xs

{-@ lmap :: (a -> b) -> xs:List a -> {ys:List b | llength xs == llength ys} / [llength xs] @-}
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
ltail _ = impossible "ltail"

{-@ lfoldr :: (a -> b -> b) -> b -> List a -> b @-}
lfoldr :: (a -> b -> b) -> b -> List a -> b
lfoldr f acc Nil = acc
lfoldr f acc (x `Cons` xs) = f x (lfoldr f acc xs)

{-@ lfoldl :: (b -> a -> b) -> b -> List a -> b @-}
lfoldl :: (b -> a -> b) -> b -> List a -> b
lfoldl f acc Nil = acc
lfoldl f acc (x `Cons` xs) = lfoldl f (f acc x) xs

{-@ predicate NonNil X = (llength X > 0) @-}
