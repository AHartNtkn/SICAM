{-# LANGUAGE
    TupleSections
 #-}

module Reduce3 where

import Data.Int
import Data.Bifunctor
import Control.Monad

import Clash.Prelude
import Clash.Signal
import GHC.Classes


-- A pair of bits

type Int2 = Unsigned 2

data InteractionOffset 
  = Zero
  | One
  | Two

splitEnv :: (KnownNat n) => SNat (n * 3) -> InteractionOffset 
         -> Vec (n * 3 + 2) a -> (Vec n (a, a, a), a, a)
splitEnv sn off vec =  
  let
    (v0, r1, r2) = case off of
      Zero -> (\(a, (b, c)) -> (a, b, c)) $ bimap id (\(a :> b :> Nil) -> (a, b)) $ splitAt sn vec
      One -> (\(a :> Nil, (b, c :> Nil)) -> (b, a, c)) $ bimap id (splitAt sn) $ splitAt d1 vec
      Two -> (\((a, b), c) -> (c, a, b)) $ bimap (\(a :> b :> Nil) -> (a, b)) id $ splitAt d2 vec

    v1 = map (\a -> (a !! 0, a !! 1, a !! 2)) $ unconcat d3 v0
  in (v1, r1, r2)

unsplitEnv :: (KnownNat n) => InteractionOffset 
           -> (Vec n (a, a, a), a, a) -> Vec (n * 3 + 2) a
unsplitEnv off (v, r1, r2) = 
  let 
    v0 = concat $ map (\(a, b, c) -> a :> b :> c :> Nil) v

    v1 = case off of
      Zero -> v0 ++ (r1 :> r2 :> Nil)
      One -> r1 :> v0 ++ (r2 :> Nil)
      Two -> r1 :> r2 :> v0
  in v1

interactionMap :: (KnownNat n) => InteractionOffset 
               -> ((a, a, a) -> ((a, a, a), k)) -> Vec (n * 3 + 2) a -> (Vec (n * 3 + 2) a, Vec n k)
interactionMap off f vec =
  let (v0, r1, r2) = splitEnv SNat off vec
      (v1, ks) = unzip $ map f v0
      v2 = unsplitEnv off (v1, r1, r2)
  in (v2, ks)