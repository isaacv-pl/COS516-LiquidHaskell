-- Red-Black Trees

data Col = R | B
data Tree a = Leaf | Node Col a (Tree a) (Tree a)

-- Color Invariant: Children of every Node R must be Node B or Leaf
{-@ measure isB :: Tree a -> Bool
    isB (Node c x l r) = c == B
    isB (Leaf) = True @-}

{-@ measure isRB :: Tree a -> Bool
    isRB (Leaf) = true
    isRB (Node c x l r) = isRB l && isRB r && c = R => (isB l && isB r) @-}

{-@ measure almostRB :: Tree a -> Bool
    almostRB (Leaf) = True
    almostRB (Node c x l r) = isRB l && isRB r @-}

-- Height Invariant: number of Node B along any path from each Node is same
{-@ measure bh :: Tree a -> Int
    bh (Leaf) = 0
    bh (Node c x l r) = bh l + if c = R then 0 else 1 @-}

{-@ measure isBal :: Tree a -> Bool
    isBal (Leaf) = True
    isBal (Node c x l r) = bh l == bh r && isBal l && isBal r @-}

-- Order Invariant: Binary-search order left <= x <= right
{-@ data Tree a <l::a->a->Bool, r::a->a->Bool> = Leaf
    | Node { c :: Col, key :: a, lt :: Tree<l,r> a<l key>, rt :: Tree<l,r> a<r key> } @-}

{-@ type OTree a = Tree <{\k v -> v<k}, {\k v -> v>k}> a @-}

{-@ type RBT a = {v:OTree a | isRB v && isBal v} @-}

{-@ type AlmostRBT a = {v:OTree a | almostRB v && isBal v} @-}

{-@ xs :: RBT Int @-}
xs :: Tree Int
xs = Node R 5 (Node B 3 Leaf Leaf) (Node B 9 Leaf Leaf)
