module SimpleRefinements where
import Language.Haskell.Liquid.Prelude


-- |Simple Refinement Types

{-@ zero :: {v:Int | v = 0} @-}
zero     :: Int
zero     =  0
