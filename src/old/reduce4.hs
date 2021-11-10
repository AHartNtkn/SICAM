{-# LANGUAGE
    TupleSections
 #-}

module Reduce4 where

import Data.Int
import Data.Bifunctor
import Control.Monad

import Clash.Prelude
import Clash.Signal
import GHC.Classes


-- A pair of bits

addressSpace = 2 ** 16

type Int2 = Unsigned 2

-- ::::::::::
-- :: Node ::
-- ::::::::::

type Link addr = (Int2, addr)

data Kind
  = AIR
  | ROOT
  | ERA
  | CON
  | DUP
  deriving (Eq)

data Node addr =
  Node Kind (Link addr) (Link addr) (Link addr)
  deriving (Eq)

getKind (Node k _ _ _) = k

getDist (Node k (p0, a0) (p1, a1) (p2, a2)) slot =
  let a | slot == 0 = a0
        | slot == 1 = a1
        | slot == 2 = a2
        | True = undefined
  in a - (addressSpace / 2)

getSlot (Node k (p0, a0) (p1, a1) (p2, a2)) slot =
  let s | slot == 0 = p0
        | slot == 1 = p1
        | slot == 2 = p2
        | True = undefined
  in s

incPort (Node k (p0, a0) (p1, a1) (p2, a2)) slot delta =
  let (a0', a1', a2') | slot == 0 = (a0 + delta, a1, a2)
                      | slot == 1 = (a0, a1 + delta, a2)
                      | slot == 2 = (a0, a1, a2 + delta)
                      | True = undefined
  in Node k (p0, a0') (p1, a1') (p2, a2')

incPorts (Node k (p0, a0) (p1, a1) (p2, a2)) slot delta =
  let (a0', a1', a2') = (a0 + delta, a1 + delta, a2 + delta)
  in Node k (p0, a0') (p1, a1') (p2, a2')

setPorts (Node k l0 l1 l2) slot newDist newSlot =
  let nd = (newSlot, newDist + (addressSpace / 2))

      (l0', l1', l2') | slot == 0 = (nd, l1, l2)
                      | slot == 1 = (l0, nd, l2)
                      | slot == 2 = (l0, l1, nd)
                      | True = undefined
  in Node k l0' l1' l2'

getForce (Node k (p0, a0) (p1, a1) (p2, a2)) =
  let x = a0 - (addressSpace / 2)
      y = a1 - (addressSpace / 2)
      z = a2 - (addressSpace / 2)
  in signum x * x ** 2 + signum y * y ** 2 + signum z * z ** 2

air = Node ROOT (0, 0) (0, 1) (0, 2)

-- :::::::::
-- :: Net ::
-- :::::::::

type Alloc addr = Vec 4 addr

-- Looks at the positions + or - 15 around the index `i`.
-- Any time it finds an empty place, it adds it to the index.
-- Also returns a Bool indicating if it was successful in finding 4 free spaces.
alloc4 :: (KnownNat n, Num len)
  => Vec n (Node addr) -> len -> addr -> Alloc addr
  -> (Bool, Alloc addr)
alloc4 net len i indxs =
  let k = 0
