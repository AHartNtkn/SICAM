{-# LANGUAGE TupleSections, DataKinds, GADTs, KindSignatures #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-redundant-constraints #-}

{-# LANGUAGE NoImplicitPrelude #-}

module Reduce where

import Data.Int
import Data.Proxy

import Data.Singletons

import Control.Monad

import Clash.Prelude
import Clash.Signal
import GHC.Classes


import GHC.TypeLits

-- Polorizations
data Pol a b 
  = Pos a
  | Neg b 
  deriving (Generic, NFDataX, Eq, Show)

{-
data Instruction n numType
  = Jump
  | Annihilate Int8 Int8
  | Duplicate Int8 Int8
  | Delete Int8
  | Literal Int8 numType
-}

-- Types characterizing the graph as layed out in memory.
type Port = Unsigned 2

type Link n = (Port, Index n)

data PosHead3
  = Abs
  | Par
  deriving (Generic, NFDataX, Eq, Show)

data PosType n numType
  = PT PosHead3 (Link n) (Link n)
  | Nul
  | Num numType
  deriving (Generic, NFDataX, Eq, Show)

data NegHead3
  = App
  | Dup
  | Add
  | Mul
  deriving (Generic, NFDataX, Eq, Show)

data ArithHead
  = AddP
  | MulP
  deriving (Generic, NFDataX, Eq, Show)

data NegType n numType
  = Del
  | NM ArithHead numType (Link n)
  | NT NegHead3 (Link n) (Link n)
  deriving (Generic, NFDataX, Eq, Show)

data Node n numType
  = Root (Link n)
  | Eq (Link n) (Link n)
  | Node (Pol (PosType n numType) (NegType n numType)) (Link n)
  deriving (Generic, NFDataX, Eq, Show)

data InterInstr n numType
  = Noop
  -- Swap two addresses and delete address 
  | ConI (Index n) (Maybe (Link n, Link n))
  -- Write node to address
  | WrtI (Index n) (Node n numType)
  deriving (Generic, NFDataX, Eq, Show)

data DupInstr n
  = NodI
  | NewI PosHead3 (Link n) (Link n) (Link n)

-- Do two heads annihilate or duplicate?
anniHeadQ Abs App = True
anniHeadQ Par Dup = True
anniHeadQ _ _ = False

-- Is a head a numerical opperation?
numHead3Q Mul = True
numHead3Q Add = True
numHead3Q _ = False

-- Do two node types annihilate?
anniNodeQ (PT ph _ _) (NT nh _ _) = anniHeadQ ph nh
anniNodeQ (PT ph _ _) _ = False
anniNodeQ Nul Del = True
anniNodeQ Nul _ = False
anniNodeQ (Num numType) (NT nh _ _) = numHead3Q nh
anniNodeQ (Num numType) (NM _ _ _) = True
anniNodeQ (Num numType) Del = True

-- Do two heads require an empty address to interact?
dupHeadQ Abs App = False
dupHeadQ Par Dup = False
dupHeadQ _ _ = True

-- Do two node require an empty address to interact?
-- Note: Assumes the second node was summoned to the first node at address j.
dupNodeQ j (Node h1 _) (Node h2 (0, k)) | j == k = case (h1, h2) of
  (Pos h1', Neg h2') -> case h1' of
    (PT ph _ _) -> case h2' of
      (NT nh _ _) -> dupHeadQ ph nh
      (NM _ _ _) -> True
      _ -> False
    _ -> False
  (Neg h2', Pos h1') -> case (h1', h2') of
    (PT ph _ _, NT nh _ _) -> dupHeadQ ph nh
dupNodeQ j _ _ = False


-- Polarizations for triple nodes.
-- False for negative polerization.
-- True for positive...
polerizationN App = (False, True)
polerizationN Dup = (True, True)
polerizationN Add = (False, True)
polerizationN Mul = (False, True)

polerizationP Abs = (True, False)
polerizationP Par = (False, False)

-- Given a node, and another node pointed at by the first's principal port,
-- generate an appropriate set of instructions
interactInterp ::
  (KnownNat n, Num numType)
  => Index n
  -> Node n numType
  -> Node n numType
  -> (Vec 2 (InterInstr n numType), Maybe (Vec 2 (DupInstr n)))
interactInterp i (Node (Pos np) (0, k)) (Node (Neg nn) (0, j)) = 
  -- Check if the summoned node points to the summoner.
  case (i == j) of 
    True -> case (np, nn) of
      -- Deletion
      (Nul, Del) -> (
          ConI i Nothing :>
          ConI k Nothing :>
          repeat Noop, Nothing)
      (Nul, NT nh l11 l12) -> case polerizationN nh of
        (True, True)   -> (WrtI i (Node (Neg Del) l11) :> WrtI k (Node (Neg Del) l12) :> repeat Noop, Nothing)
        (True, False)  -> (WrtI i (Node (Neg Del) l11) :> WrtI k (Node (Pos Nul) l12) :> repeat Noop, Nothing)
        (False, True)  -> (WrtI i (Node (Pos Nul) l11) :> WrtI k (Node (Neg Del) l12) :> repeat Noop, Nothing)
        (False, False) -> (WrtI i (Node (Pos Nul) l11) :> WrtI k (Node (Pos Nul) l12) :> repeat Noop, Nothing)
      (PT ph l21 l22, Del) -> case polerizationP ph of
        (True, True)   -> (WrtI i (Node (Neg Del) l21) :> WrtI k (Node (Neg Del) l22) :> repeat Noop, Nothing)
        (True, False)  -> (WrtI i (Node (Neg Del) l21) :> WrtI k (Node (Pos Nul) l22) :> repeat Noop, Nothing)
        (False, True)  -> (WrtI i (Node (Pos Nul) l21) :> WrtI k (Node (Neg Del) l22) :> repeat Noop, Nothing)
        (False, False) -> (WrtI i (Node (Pos Nul) l21) :> WrtI k (Node (Pos Nul) l22) :> repeat Noop, Nothing)
      (Nul, NM _ _ l) -> (WrtI i (Node (Pos Nul) l) :> ConI k Nothing :> repeat Noop, Nothing)
                      -- (ConI k (i, l) :> repeat Noop, Nothing) ???
      (Num _, Del) -> (ConI i Nothing :> ConI k Nothing :> repeat Noop, Nothing)

      -- Evaluation
      (Num n, NT Add l11 l12) -> (
        WrtI i (Node (Neg $ NM AddP n l12) l11) :> 
        ConI k Nothing :>
        repeat Noop, Nothing)
      (Num n, NT Mul l11 l12) -> (
        WrtI i (Node (Neg $ NM MulP n l12) l11) :> 
        ConI k Nothing :>
        repeat Noop, Nothing)
      (Num n, NM AddP m l) -> (
        WrtI i (Node (Pos $ Num (n + m)) l) :> 
        ConI k Nothing :>
        repeat Noop, Nothing)
      (Num n, NM MulP m l) -> (
        WrtI i (Node (Pos $ Num (n * m)) l) :> 
        ConI k Nothing :>
        repeat Noop, Nothing)

      -- Duplication and Application
      (PT ph l21 l22, NT nh l11 l12) -> case anniHeadQ ph nh of
        True -> (
          ConI i (Just (l21, l11)) :> 
          ConI k (Just (l22, l12)) :> 
          repeat Noop, Nothing)
        False -> (
          WrtI i (Node (Neg $ NT nh undefined undefined) l21) :>
          WrtI k (Node (Neg $ NT nh undefined undefined) l22) :>
          repeat Noop, Just $ 
          NewI ph (1, i) (1, k) l11 :>
          NewI ph (2, i) (2, k) l12 :>
          Nil)

      (PT ph l21 l22, NM nh n l12) -> (
          WrtI i (Node (Neg $ NM nh n undefined) l21) :> 
          WrtI k (Node (Neg $ NM nh n undefined) l22) :>
          repeat Noop, Just $ 
          NewI ph (1, i) (1, k) l12 :>
          repeat NodI
          )

      (Num n, NT nh l11 l12) -> (
        WrtI i (Node (Pos $ Num n) l11) :> 
        WrtI k (Node (Pos $ Num n) l12) :> 
        repeat Noop, Nothing)
    False -> (repeat Noop, Nothing)
interactInterp i _ _ = (repeat Noop, Nothing)

-- Given a node, and another node pointed at by the first's principal port,
-- generate an appropriate set of instructions
interactInterpS ::
  (KnownNat n, Num numType)
  => Index n
  -> Node n numType
  -> Node n numType
  -> ( Vec 2 (Index n, NodeInstr n numType)
     , Vec 4 (Index n, Maybe (Link n))
     , Vec 4 (Index n, Maybe (Link n))
     , Vec 4 (Index n, Maybe (Link n))
     , Vec 2 (DupInstr n))
interactInterpS i (Node (Pos np) (0, k)) (Node (Neg nn) (0, j)) = 
  let
    def x = (x,
             repeat (maxBound, Nothing),
             repeat (maxBound, Nothing),
             repeat (maxBound, Nothing),
             repeat NodI)
  -- Check if the summoned node points to the summoner.
  in case (i == j) of 
    True -> case (np, nn) of
      -- Deletion
      (Nul, Del) -> def $ (i, ClrNI) :> (k, ClrNI) :> Nil
      (Nul, NT nh l11 l12) -> case polerizationN nh of
        (True, True)   -> def $ 
          (i, WrtNI $ Node (Neg Del) l11) :> (k, WrtNI $ Node (Neg Del) l12) :> Nil
        (True, False)  -> def $ 
          (i, WrtNI $ Node (Neg Del) l11) :> (k, WrtNI $ Node (Pos Nul) l12) :> Nil
        (False, True)  -> def $ 
          (i, WrtNI $ Node (Pos Nul) l11) :> (k, WrtNI $ Node (Neg Del) l12) :> Nil
        (False, False) -> def $ 
          (i, WrtNI $ Node (Pos Nul) l11) :> (k, WrtNI $ Node (Pos Nul) l12) :> Nil
      (PT ph l21 l22, Del) -> case polerizationP ph of
        (True, True)   -> def $ 
          (i, WrtNI $ Node (Neg Del) l21) :> (k, WrtNI $ Node (Neg Del) l22) :> Nil
        (True, False)  -> def $ 
          (i, WrtNI $ Node (Neg Del) l21) :> (k, WrtNI $ Node (Pos Nul) l22) :> Nil
        (False, True)  -> def $ 
          (i, WrtNI $ Node (Pos Nul) l21) :> (k, WrtNI $ Node (Neg Del) l22) :> Nil
        (False, False) -> def $ 
          (i, WrtNI $ Node (Pos Nul) l21) :> (k, WrtNI $ Node (Pos Nul) l22) :> Nil
      (Nul, NM _ _ l) -> def $ 
          (i, WrtNI $ Node (Pos Nul) l) :> (k, ClrNI) :> Nil
      (Num _, Del) -> def $ 
          (i, ClrNI) :> (k, ClrNI) :> Nil

      -- Evaluation
      (Num n, NT Add l11 l12) -> def $ 
          (i, WrtNI $ Node (Neg $ NM AddP n l12) l11) :> (k, ClrNI) :> Nil
      (Num n, NT Mul l11 l12) -> def $ 
          (i, WrtNI $ Node (Neg $ NM MulP n l12) l11) :> (k, ClrNI) :> Nil
      (Num n, NM AddP m l) -> def $ 
          (i, WrtNI $ Node (Pos $ Num (n + m)) l) :> (k, ClrNI) :> Nil
      (Num n, NM MulP m l) -> def $ 
          (i, WrtNI $ Node (Pos $ Num (n * m)) l) :> (k, ClrNI) :> Nil

      -- Duplication and Application
      (PT ph l21 l22, NT nh l11 l12) -> case anniHeadQ ph nh of
        True -> 
          let
            (p1, p3, pi21) = case l21 of
              (0, i) -> ((i, Just l11), (maxBound, Nothing), (maxBound, Nothing))
              (1, i) -> ((maxBound, Nothing), (i, Just l11), (maxBound, Nothing))
              (2, i) -> ((maxBound, Nothing), (maxBound, Nothing), (i, Just l11))
              (3, i) -> ((maxBound, Nothing), (maxBound, Nothing), (maxBound, Nothing))

            (pi02, pi12, pi22) = case l11 of
              (0, i) -> ((i, Just l21), (maxBound, Nothing), (maxBound, Nothing))
              (1, i) -> ((maxBound, Nothing), (i, Just l21), (maxBound, Nothing))
              (2, i) -> ((maxBound, Nothing), (maxBound, Nothing), (i, Just l21))
              (3, i) -> ((maxBound, Nothing), (maxBound, Nothing), (maxBound, Nothing))

            (pi03, pi13, pi23) = case l22 of
              (0, i) -> ((i, Just l12), (maxBound, Nothing), (maxBound, Nothing))
              (1, i) -> ((maxBound, Nothing), (i, Just l12), (maxBound, Nothing))
              (2, i) -> ((maxBound, Nothing), (maxBound, Nothing), (i, Just l12))
              (3, i) -> ((maxBound, Nothing), (maxBound, Nothing), (maxBound, Nothing))

            (pi04, pi14, pi24) = case l12 of
              (0, i) -> ((i, Just l22), (maxBound, Nothing), (maxBound, Nothing))
              (1, i) -> ((maxBound, Nothing), (i, Just l22), (maxBound, Nothing))
              (2, i) -> ((maxBound, Nothing), (maxBound, Nothing), (i, Just l22))
              (3, i) -> ((maxBound, Nothing), (maxBound, Nothing), (maxBound, Nothing))
          in (
           repeat (maxBound, NopNI), 
           p1 :> pi02 :> pi03 :> pi04 :> Nil,
           p3 :> pi12 :> pi13 :> pi14 :> Nil,
           pi21 :> pi22 :> pi23 :> pi24 :> Nil,
           repeat NodI)
        False -> (
          (i, WrtNI $ Node (Neg $ NT nh undefined undefined) l21) :>
          (k, WrtNI $ Node (Neg $ NT nh undefined undefined) l22) :> Nil,
          repeat (maxBound, Nothing),
          repeat (maxBound, Nothing),
          repeat (maxBound, Nothing),
          NewI ph (1, i) (1, k) l11 :>
          NewI ph (2, i) (2, k) l12 :> Nil)

      (PT ph l21 l22, NM nh n l12) -> (
          (i, WrtNI $ Node (Neg $ NM nh n undefined) l21) :>
          (k, WrtNI $ Node (Neg $ NM nh n undefined) l22) :> Nil,
          repeat (maxBound, Nothing),
          repeat (maxBound, Nothing),
          repeat (maxBound, Nothing),
          NewI ph (1, i) (1, k) l12 :>
          repeat NodI)

      (Num n, NT nh l11 l12) -> def $ 
          (i, WrtNI $ Node (Pos $ Num n) l11) :>
          (k, WrtNI $ Node (Pos $ Num n) l12) :> Nil
    False -> def $ repeat (maxBound, NopNI)
interactInterpS i _ _ = (repeat (maxBound, NopNI), repeat (maxBound, Nothing), repeat (maxBound, Nothing), repeat (maxBound, Nothing), repeat NodI)


-- Given a node, and another node pointed at by the first's principal port,
-- generate an appropriate set of instructions
{-
interactInterpD ::
  (KnownNat n, Num numType)
  => Maybe (Index n)
  -> Index n
  -> Node n numType
  -> Node n numType
  -> Vec 2 (Index (n + 1), Maybe (Node n numType))
interactInterpD e i (Node pol1 (0, k)) (Node pol2 (0, j)) = undefined
interactInterpD e i (Eq l1 (s, j)) n = case n of
  Root _ -> (resize j, Just $ Root l1) :> (resize i, Nothing) :> Nil
  Node pol pr -> 
    if s == 0
    then (resize j, Just $ Node pol l1) :> (resize i, Nothing) :> Nil
    else case pol of
      

case s of
    0 -> (resize j, Just $ Node pol l1) :> (resize i, Nothing) :> Nil
    1 -> undefined
    2 -> undefined
    3 -> repeat (maxBound, Nothing)
  _ -> repeat (maxBound, Nothing)
interactInterpD e i _ _ = repeat (maxBound, Nothing)
-}

{-
  let
    def x = (x,
             repeat (maxBound, Nothing),
             repeat (maxBound, Nothing),
             repeat (maxBound, Nothing))
  -- Check if the summoned node points to the summoner.
  in case (i == j) of 
    True -> case (np, nn) of
      -- Deletion
      (Nul, Del) -> def $ (i, ClrNI) :> (k, ClrNI) :> Nil
      (Nul, NT nh l11 l12) -> case polerizationN nh of
        (True, True)   -> def $ 
          (i, WrtNI $ Node (Neg Del) l11) :> (k, WrtNI $ Node (Neg Del) l12) :> Nil
        (True, False)  -> def $ 
          (i, WrtNI $ Node (Neg Del) l11) :> (k, WrtNI $ Node (Pos Nul) l12) :> Nil
        (False, True)  -> def $ 
          (i, WrtNI $ Node (Pos Nul) l11) :> (k, WrtNI $ Node (Neg Del) l12) :> Nil
        (False, False) -> def $ 
          (i, WrtNI $ Node (Pos Nul) l11) :> (k, WrtNI $ Node (Pos Nul) l12) :> Nil
      (PT ph l21 l22, Del) -> case polerizationP ph of
        (True, True)   -> def $ 
          (i, WrtNI $ Node (Neg Del) l21) :> (k, WrtNI $ Node (Neg Del) l22) :> Nil
        (True, False)  -> def $ 
          (i, WrtNI $ Node (Neg Del) l21) :> (k, WrtNI $ Node (Pos Nul) l22) :> Nil
        (False, True)  -> def $ 
          (i, WrtNI $ Node (Pos Nul) l21) :> (k, WrtNI $ Node (Neg Del) l22) :> Nil
        (False, False) -> def $ 
          (i, WrtNI $ Node (Pos Nul) l21) :> (k, WrtNI $ Node (Pos Nul) l22) :> Nil
      (Nul, NM _ _ l) -> def $ 
          (i, WrtNI $ Node (Pos Nul) l) :> (k, ClrNI) :> Nil
      (Num _, Del) -> def $ 
          (i, ClrNI) :> (k, ClrNI) :> Nil

      -- Evaluation
      (Num n, NT Add l11 l12) -> def $ 
          (i, WrtNI $ Node (Neg $ NM AddP n l12) l11) :> (k, ClrNI) :> Nil
      (Num n, NT Mul l11 l12) -> def $ 
          (i, WrtNI $ Node (Neg $ NM MulP n l12) l11) :> (k, ClrNI) :> Nil
      (Num n, NM AddP m l) -> def $ 
          (i, WrtNI $ Node (Pos $ Num (n + m)) l) :> (k, ClrNI) :> Nil
      (Num n, NM MulP m l) -> def $ 
          (i, WrtNI $ Node (Pos $ Num (n * m)) l) :> (k, ClrNI) :> Nil

      -- Duplication and Application
      (PT ph l21 l22, NT nh l11 l12) -> case anniHeadQ ph nh of
        True -> 
          let
            (p1, p3, pi21) = case l21 of
              (0, i) -> ((i, Just l11), (maxBound, Nothing), (maxBound, Nothing))
              (1, i) -> ((maxBound, Nothing), (i, Just l11), (maxBound, Nothing))
              (2, i) -> ((maxBound, Nothing), (maxBound, Nothing), (i, Just l11))
              (3, i) -> ((maxBound, Nothing), (maxBound, Nothing), (maxBound, Nothing))

            (pi02, pi12, pi22) = case l11 of
              (0, i) -> ((i, Just l21), (maxBound, Nothing), (maxBound, Nothing))
              (1, i) -> ((maxBound, Nothing), (i, Just l21), (maxBound, Nothing))
              (2, i) -> ((maxBound, Nothing), (maxBound, Nothing), (i, Just l21))
              (3, i) -> ((maxBound, Nothing), (maxBound, Nothing), (maxBound, Nothing))

            (pi03, pi13, pi23) = case l22 of
              (0, i) -> ((i, Just l12), (maxBound, Nothing), (maxBound, Nothing))
              (1, i) -> ((maxBound, Nothing), (i, Just l12), (maxBound, Nothing))
              (2, i) -> ((maxBound, Nothing), (maxBound, Nothing), (i, Just l12))
              (3, i) -> ((maxBound, Nothing), (maxBound, Nothing), (maxBound, Nothing))

            (pi04, pi14, pi24) = case l12 of
              (0, i) -> ((i, Just l22), (maxBound, Nothing), (maxBound, Nothing))
              (1, i) -> ((maxBound, Nothing), (i, Just l22), (maxBound, Nothing))
              (2, i) -> ((maxBound, Nothing), (maxBound, Nothing), (i, Just l22))
              (3, i) -> ((maxBound, Nothing), (maxBound, Nothing), (maxBound, Nothing))
          in (
           repeat (maxBound, NopNI), 
           p1 :> pi02 :> pi03 :> pi04 :> Nil,
           p3 :> pi12 :> pi13 :> pi14 :> Nil,
           pi21 :> pi22 :> pi23 :> pi24 :> Nil)
        False -> (
          (i, WrtNI $ Node (Neg $ NT nh undefined undefined) l21) :>
          (k, WrtNI $ Node (Neg $ NT nh undefined undefined) l22) :> Nil,
          repeat (maxBound, Nothing),
          repeat (maxBound, Nothing),
          repeat (maxBound, Nothing),


          NewI ph (1, i) (1, k) l11 :>
          NewI ph (2, i) (2, k) l12 :> Nil)

      (PT ph l21 l22, NM nh n l12) -> (
          (i, WrtNI $ Node (Neg $ NM nh n undefined) l21) :>
          (k, WrtNI $ Node (Neg $ NM nh n undefined) l22) :> Nil,
          repeat (maxBound, Nothing),
          repeat (maxBound, Nothing),
          repeat (maxBound, Nothing),
          NewI ph (1, i) (1, k) l12 :>
          repeat NodI)

      (Num n, NT nh l11 l12) -> def $ 
          (i, WrtNI $ Node (Pos $ Num n) l11) :>
          (k, WrtNI $ Node (Pos $ Num n) l12) :> Nil
    False -> def $ repeat (maxBound, NopNI)
interactInterpD e i _ _ = (repeat (maxBound, NopNI), repeat (maxBound, Nothing), repeat (maxBound, Nothing), repeat (maxBound, Nothing))
-}

trySwap :: Eq a => (a, a) -> a -> a -> a
trySwap (a, b) c d | a == c = b
                   | b == c = a
                   | True = d

-- Transform a node according to a single instruction
execInstr ::
  (KnownNat n, Num numType)
  => Index n
  -> InterInstr n numType
  -> Maybe (Node n numType)
  -> Maybe (Node n numType)
execInstr i instr nd = case instr of
  Noop -> nd
  WrtI j md -> case i == j of
    True -> Just md
    False -> nd
  ConI j m -> case (i == j, m, nd) of
    (_, _, Nothing) -> Nothing
    (True, _, _) -> Nothing
    (False, Nothing, Just nd') -> Just nd'
    (False, Just s, Just nd') -> Just $ case nd' of
      Root l3 -> Root (trySwap s (0, i) l3)
      Node (Pos pt) l3 -> (\h -> Node (Pos h) (trySwap s (0, i) l3)) $ case pt of
        Nul -> Nul
        PT ph l4 l5 -> PT ph (trySwap s (1, i) l4) (trySwap s (2, i) l5) 
        Num n -> Num n
      Node (Neg nt) l3 -> (\h -> Node (Neg h) (trySwap s (0, i) l3)) $ case nt of
        Del -> Del
        NM ah n l4 -> NM ah n (trySwap s (1, i) l4)
        NT nh l4 l5 -> NT nh (trySwap s (1, i) l4) (trySwap s (2, i) l5) 

data NodeInstr n numType
  = NopNI
  | WrtNI (Node n numType)
  | ClrNI
  deriving (Generic, NFDataX, Eq, Show)

data PortInstr n
  = NopPI
  | WrtPI (Link n)
  deriving (Generic, NFDataX, Eq, Show)

-- Transform a node according to an organized collection of instructions
execInstr3 ::
  (KnownNat n, Num numType)
  => Index n
  -> (NodeInstr n numType, Maybe (Link n), Maybe (Link n), Maybe (Link n))
  -> Node n numType
  -> Maybe (Node n numType)
execInstr3 i (n, pi0, pi1, pi2) nd = 
  let
    nd' = case n of
      NopNI -> Just nd
      WrtNI m -> Just m
      ClrNI -> Nothing
  in nd' >>= \x -> return $ case x of
      Root l3 -> Root (maybe l3 id pi0)
      Node (Pos pt) l3 -> (\h -> Node (Pos h) (maybe l3 id pi0)) $ case pt of
        Nul -> Nul
        PT ph l4 l5 -> PT ph (maybe l4 id pi1) (maybe l5 id pi2)
        Num n -> Num n
      Node (Neg nt) l3 -> (\h -> Node (Neg h) (maybe l3 id pi0)) $ case nt of
        Del -> Del
        NM ah n l4 -> NM ah n (maybe l4 id pi1)
        NT nh l4 l5 -> NT nh (maybe l4 id pi1) (maybe l5 id pi2)

-- Execute a sequence of instructions on a single node.
execAssem ::
  (KnownNat n, KnownNat m, Num numType)
  => Index n
  -> Vec m (InterInstr n numType)
  -> Maybe (Node n numType)
  -> Maybe (Node n numType)
execAssem i v nd = foldr (\e r -> execInstr i e r) nd v

sortPorts ::
  (Num numType, KnownNat n)
  => Vec (2 ^ n) (Index (2 ^ n))
  -> Vec (2 ^ n) (Maybe (Node (2 ^ n) numType))
  -> Vec (2 ^ n) (Maybe (Index (2 ^ n)))
--Vec n (Maybe (Node n numType))
--  -> Vec (n * 4) (InterInstr n numType)
sortPorts range mem = 
  let princIndex (Node _ (_, i)) = i
      princIndex (Root (_, i)) = i
      princIndex (Eq _ (_, i)) = i

      -- Indexes of principal ports
      ppIndx = map (maybe 0 princIndex) mem

      -- Nodes moved to wherever a principal port points to them
      -- :: Vec n (Maybe (Node n numType))
      sports = gather mem ppIndx
      
      -- A list of instructions generated from 
      -- :: Vec (n * 4) (InterInstr n numType)
      --instru = concat $ zipWith3 (((.).(.)) (maybe (repeat Noop) id) . liftM2 . interactInterp) range mem sports

      -- Get empty addresses
      empties = imap (\i -> maybe (Just i) (const Nothing)) mem

      -- Get addresses which require empty addresses for duplication.
      dups = izipWith (\i a b -> liftM2 (dupNodeQ i) a b >>= \r -> if r then Just i else Nothing) mem sports

      -- Memory with empty addresses placed where duplicators need them.
      dupReadyEmpties = unknownGatherScatter dups empties
  in dupReadyEmpties





{-
Given a sparse memory with data randomly distributed, unknownGather will bubble the
nonempty values to the front, though it doesn't preserve order. This is useful for
gathering sparse data where the indexes of said data are unknown.

This creates a log-depth circuit.

DenseMem is an ordered pair consisting of, firstly, a vector which has dense data
followed by Nothing and, secondly, the index at which the Nothing starts.
-}
data DenseMem (a :: Type) (f :: TyFun Nat Type) :: Type
type instance Apply (DenseMem a) k = (Vec (2 ^ k) (Maybe a), Index ((2 ^ k) + 1))

unknownGather' :: forall k a . KnownNat k => Vec (2 ^ k) (Maybe a) -> (Vec (2 ^ k) (Maybe a), Index ((2 ^ k) + 1))
unknownGather' = dtfold (Proxy :: Proxy (DenseMem a)) base step where
  base Nothing = (Nothing :> Nil, 0)
  base (Just a) = (Just a :> Nil, 1)

  denseMemFuse j vi vj = rotateRight (vi ++ reverse vj) j

  step :: SNat l -> DenseMem a @@ l -> DenseMem a @@ l -> DenseMem a @@ (l+1)
  step SNat (v1, i) (v2, j) = (denseMemFuse j v1 v2, resize i + resize j)

unknownGather :: forall k a . KnownNat k => Vec (2 ^ k) (Maybe a) -> Vec (2 ^ k) (Maybe a)
unknownGather = fst . unknownGather'

-- Given two random memories of addresses and data, gather addresses
-- and data into a dense form and scatter data according to those addresses.
unknownGatherScatter :: forall k b . KnownNat k => 
  Vec (2 ^ k) (Maybe (Index (2 ^ k))) -> Vec (2 ^ k) (Maybe b) -> Vec (2 ^ k) (Maybe b)
unknownGatherScatter addr cont =
  let (addr', cont') = (unknownGather addr, unknownGather cont)
  -- Note: maxBound points to a junk address deleted by 'init'. Is there a better way to do that?
  in init $ scatter (repeat Nothing) (map (maybe (maxBound :: Index (2 ^ k + 1)) resize) addr') cont'









-- Insert a new node at the first empty address.
newNode mem n = findIndex fst mem >>= \i -> return $ replace i n mem

{-
proc :: (Num numType, Num schedulePointer, Num exitPointer
        ,KnownNat nm, KnownNat ns, KnownNat ne, KnownNat ni)
     => Vec nm (Bool, Node n numType)
     -> (ScheduleStack n ns schedulePointer
        ,ExitStack ne exitPointer
        ,Link n)
     -> Vec ni numType
     -> ((ScheduleStack n ns schedulePointer
         ,ExitStack ne exitPointer
         ,Link n), 
        numType)
proc memory (schedule, exits, next) _ = ((schedule', exits', next'), result)
  where
  schedule' = (0, repeat undefined)

  exits' = (0, repeat undefined)
 
  next' = undefined

  result = 0



rewrite mem schedule exits (Ter k1 l10 l11 l12) (Ter k2 l20 l21 l22) =
  case k1 == k2 of
    True -> undefined
    False -> undefined


idTestMem :: Vec 4 (Bool, Node Int16 Int32)
idTestMem = map (\x -> (False, x)) d where
  d = Uni Root (2, 1)
      :> Ter Con (0, 2) (0, 3) (0, 0)
      :> Ter Con (0, 1) (2, 2) (1, 2)
      :> Ter Con (1, 2) (2, 3) (1, 3)
      :> Nil

skkTestMem :: Vec 20 (Bool, Node Int16 Int32)
skkTestMem = (map (\x -> (False, x)) d) ++ repeat (True, undefined) where
  d = Uni Root (2, 1)
      :> Ter Con (2, 2) (0, 15) (0, 0)
      :> Ter Con (2, 3) (0, 13) (0, 1)
      :> Ter Con (0, 4) (0, 11) (0, 2)
      :> Ter Con (0, 3) (0, 9) (0, 5)
      :> Ter Con (2, 4) (0, 10) (0, 6)
      :> Ter Con (2, 5) (0, 7) (2, 8)
      :> Ter Dup (1, 6) (1, 9) (1, 10)
      :> Ter Con (2, 9) (2, 10) (2, 6)
      :> Ter Con (1, 4) (1, 7) (0, 8)
      :> Ter Con (1, 5) (2, 7) (1, 8)
      :> Ter Con (1, 3) (2, 12) (0, 12)
      :> Ter Con (2, 11) (1, 12) (1, 11)
      :> Ter Con (1, 2) (2, 14) (0, 14)
      :> Ter Con (2, 13) (0, 16) (1, 13)
      :> Ter Con (1, 1) (2, 15) (1, 15)
      :> Uni Del (1, 14)
      :> Nil

results :: 
  (KnownDomain dom, 
   IP (HiddenClockName dom) (Clock dom),
   IP (HiddenEnableName dom) (Enable dom),
   IP (HiddenResetName dom) (Reset dom)) =>
   Signal dom Int32
results =
  let mem = idTestMem
      exits = repeat @10 undefined
      schedule = repeat @10 undefined
  in mealy (proc mem) ((0 :: Int8, schedule), (0 :: Int8, exits), enter mem (0, 0)) (pure (repeat @5 0))
-}