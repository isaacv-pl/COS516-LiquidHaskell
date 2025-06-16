module SimpleRefinements where
import Language.Haskell.Liquid.Prelude

{-@ zero :: {v:Int | v = 0} @-}
zero     :: Int
zero     =  0
