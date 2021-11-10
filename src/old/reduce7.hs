{-# LANGUAGE TupleSections, DataKinds, GADTs, KindSignatures #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-redundant-constraints #-}

{-# LANGUAGE NoImplicitPrelude #-}

-- stack exec --package clash-ghc -- clashi

module Reduce7 where

import Data.Int
import Data.Proxy
import Data.Maybe
import Data.Bifunctor

import Data.Singletons

import Control.Monad

import Clash.Prelude
import Clash.Signal
import Clash.Sized.Internal.Index
import Clash.Sized.BitVector
import Clash.Sized.Unsigned
import GHC.Classes


import GHC.TypeLits

data ALUHead
  = Add
  | Mul
  deriving (Generic, NFDataX, Eq, Show)

data Kind
  = Nan
  | Equ
  | Rot

  | Era
  | Con
  | Dup

  | Num
  | Alu ALUHead

  | Key
  | Scr
  deriving (Generic, NFDataX, Eq, Show)

isAluKind (Alu _) = True
isAluKind _ = False

type Link n = (BitVector 2, Index (2 ^ n))

-- Convert a port to an index for index modification.
uidx :: KnownNat n => BitVector 2 -> Index n
uidx 0 = 0
uidx 1 = 1
uidx 2 = 2
uidx 3 = undefined

linkMemAddr :: KnownNat n => Link n -> Index (3 * 2 ^ n)
linkMemAddr (n, a) =
  let m = case n of
            0 -> 0
            1 -> 1
            2 -> 2
            3 -> undefined
  in 3 * resize a + m

type Node n = (Kind, Vec 3 (Link n))
type Memory n = Vec (2 ^ n) (Node n)

type NumFormat n = BitVector (2 * n + 4)

numFormat :: (KnownNat n) => NumFormat n -> (Link n, Link n)
numFormat = bitCoerce

numUnformat :: (KnownNat n) => (Link n, Link n) -> NumFormat n
numUnformat = bitCoerce









-- ====== Interaction =======

type KindInstruction n = (Index (2 ^ n), Kind)
type LinkInstruction n = (Index (3 * 2 ^ n), Link n)

annihilationCheck x y = x == y

annihilationInteraction :: forall n . (KnownNat n)
  => Vec 4 (Node n)
  -> ( Maybe (KindInstruction n)
     , Vec 8 (Maybe (LinkInstruction n)) )
annihilationInteraction 
  (  (k1, l11@(s11, a11) :> l12@(s12, a12) :> l13@(s13, a13) :> Nil)
  :> (k2, l21@(s21, a21) :> l22@(s22, a22) :> l23@(s23, a23) :> Nil)
  :> (k3, l31@(s31, a31) :> l32@(s32, a32) :> l33@(s33, a33) :> Nil)
  :> (k4, l41@(s41, a41) :> l42@(s42, a42) :> l43@(s43, a43) :> Nil)
  :> Nil )
  = undefined





duplicationCheck x y = 
  let comp x y =
        x == Era || 
        (x == Dup && y == Con) ||
        ((x == Dup || x == Con) && (y == Scr || y == Key || y == Num || y == Era))
  in comp x y || comp y x

duplicationInteraction :: forall n . (KnownNat n)
  => Maybe (Index (2 ^ n))
  -> Vec 4 (Node n)
  -> ( Vec 3 (Maybe (KindInstruction n))
     , Vec 8 (Maybe (LinkInstruction n)) )
duplicationInteraction mt
  (  (k1, l11@(s11, a11) :> l12@(s12, a12) :> l13@(s13, a13) :> Nil)
  :> (k2, l21@(s21, a21) :> l22@(s22, a22) :> l23@(s23, a23) :> Nil)
  :> (k3, l31@(s31, a31) :> l32@(s32, a32) :> l33@(s33, a33) :> Nil)
  :> (k4, l41@(s41, a41) :> l42@(s42, a42) :> l43@(s43, a43) :> Nil)
  :> Nil )
  = undefined




equCheck x = x == Equ

equInteraction :: forall n . (KnownNat n)
  => Vec 4 (Node n)
  -> ( Maybe (KindInstruction n)
     , Vec 8 (Maybe (LinkInstruction n)) )
equInteraction 
  (  (k1, l11@(s11, a11) :> l12@(s12, a12) :> l13@(s13, a13) :> Nil)
  :> (k2, l21@(s21, a21) :> l22@(s22, a22) :> l23@(s23, a23) :> Nil)
  :> (k3, l31@(s31, a31) :> l32@(s32, a32) :> l33@(s33, a33) :> Nil)
  :> (k4, l41@(s41, a41) :> l42@(s42, a42) :> l43@(s43, a43) :> Nil)
  :> Nil )
  = undefined






type ScreenInstruction n = NumFormat n

screenCheck x y = 
  let comp x y = (x == Scr) && (y == Num || y == Key)
  in comp x y || comp y x

screenInteraction :: forall n . (KnownNat n)
  => Vec 4 (Node n)
  -> ( Maybe (KindInstruction n)
     , Vec 8 (Maybe (LinkInstruction n))
     , Maybe (ScreenInstruction n) )
screenInteraction 
  (  (k1, l11@(s11, a11) :> l12@(s12, a12) :> l13@(s13, a13) :> Nil)
  :> (k2, l21@(s21, a21) :> l22@(s22, a22) :> l23@(s23, a23) :> Nil)
  :> (k3, l31@(s31, a31) :> l32@(s32, a32) :> l33@(s33, a33) :> Nil)
  :> (k4, l41@(s41, a41) :> l42@(s42, a42) :> l43@(s43, a43) :> Nil)
  :> Nil )
  = undefined



aluOp :: KnownNat n => ALUHead -> NumFormat n -> NumFormat n -> NumFormat n
aluOp h = case h of
  Add -> (+)
  Mul -> (*)

aluCheck x y = isAluKind x && y == Num

aluInteraction ::forall n . (KnownNat n)
  => Vec 4 (Node n)
  -> ( Vec 3 (Maybe (KindInstruction n))
     , Vec 8 (Maybe (LinkInstruction n)) )
aluInteraction 
  (  (Alu m, l10@(s10, a10) :> l11@(s11, a11) :> l12@(s12, a12) :> Nil)
  :> (k2,    l20@(s20, a20) :> l21@(s21, a21) :> l22@(s22, a22) :> Nil)
  :> (k3,    l30@(s30, a30) :> l31@(s31, a31) :> l32@(s32, a32) :> Nil)
  :> (k4,    l40@(s40, a40) :> l41@(s41, a41) :> l42@(s42, a42) :> Nil)
  :> Nil )
  = case s12 of
      3 -> -- There's already a second `Num` queued at a13
        let (n1, n2) = 
              ( numUnformat (l41, l42)
              , numUnformat (l21, l22) )
            (r1, r2)  = numFormat $ aluOp m n1 n2
        in (  Just (a20, Num) -- ALU instr becomes number
           :> Just (a12, Nan) -- First argument is used
           :> Just (a10, Nan) -- Second argument is used
           :> repeat Nothing

           ,  Just (linkMemAddr (0, a20), l11) -- Change principal port to former output
           :> Just (linkMemAddr l11, (0, a20)) -- Connect above
           :> Just (linkMemAddr (1, a20), r1) -- Place number values
           :> Just (linkMemAddr (2, a20), r2) -- Cont...
           :> repeat Nothing )

      -- The first argument is being instantiated
      _ -> ( repeat Nothing

           ,  Just (linkMemAddr (2, a20), (3, a10)) -- Swap principal and ancillary ports
           :> Just (linkMemAddr (0, a20), l12)      -- while marking queued argument.
           :> Just (linkMemAddr l10, (2, a20))
           :> Just (linkMemAddr l12, (0, a20))
           :> repeat Nothing )

type KeyInstruction n = NumFormat n

keyCheck x = x == Key

keyInteraction :: forall n . (KnownNat n)
  => NumFormat n 
  -> Vec 4 (Node n)
  -> ( Maybe (KindInstruction n)
     , Vec 8 (Maybe (LinkInstruction n))
     , Maybe (KeyInstruction n) )
keyInteraction key 
  (  (k1, l11@(s11, a11) :> l12@(s12, a12) :> l13@(s13, a13) :> Nil)
  :> (k2, l21@(s21, a21) :> l22@(s22, a22) :> l23@(s23, a23) :> Nil)
  :> (k3, l31@(s31, a31) :> l32@(s32, a32) :> l33@(s33, a33) :> Nil)
  :> (k4, l41@(s41, a41) :> l42@(s42, a42) :> l43@(s43, a43) :> Nil)
  :> Nil )
  = undefined




interaction :: forall n . (KnownNat n)
  => NumFormat n 
  -> Maybe (Index (2 ^ n))
  -> Index (2 ^ n)
  -> Vec 4 (Node n)
  -> ( Vec 3 (Maybe (KindInstruction n))
     , Vec 8 (Maybe (LinkInstruction n))
     , Maybe (KeyInstruction n)
     , Maybe (ScreenInstruction n) )
interaction key mt i p@((x, _) :> (y, (n, j) :> _) :> _) =
  if n == 0 && i == j
  then if duplicationCheck x y
       then (\(a, b) -> (a, b, Nothing, Nothing)) $ duplicationInteraction mt p

       else if equCheck x
       then (\(a, b) -> (a :> repeat Nothing, b, Nothing, Nothing)) $ equInteraction p

       else if annihilationCheck x y
       then (\(a, b) -> (a :> repeat Nothing, b, Nothing, Nothing)) $ annihilationInteraction p

       else if aluCheck x y
       then (\(a, b) -> (a, b, Nothing, Nothing)) $ aluInteraction p

       else if keyCheck x
       then (\(a, b, c) -> (a :> repeat Nothing, b, c, Nothing)) $ keyInteraction key p

       else if screenCheck x y
       then (\(a, b, c) -> (a :> repeat Nothing, b, Nothing, c)) $ screenInteraction p

       else (repeat Nothing, repeat Nothing, Nothing, Nothing)
  else (repeat Nothing, repeat Nothing, Nothing, Nothing)

