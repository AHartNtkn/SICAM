{-# LANGUAGE TupleSections, DataKinds, GADTs, KindSignatures #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-redundant-constraints #-}

{-# LANGUAGE NoImplicitPrelude #-}

-- stack exec --package clash-ghc -- clashi

module Reduce5 where

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

scatterWithGarbage :: (KnownNat n, KnownNat m) =>
     Vec n a -> Vec m (Index (n + 1)) -> Vec (m + k) a -> Vec n a
scatterWithGarbage def idxs dat = init $ scatter (def ++ undefined :> Nil) idxs dat


data Kind
  = Nan
  | Equ

  | Rot
  | Era
  | Nul
  | Abs
  | App
  | Dup
  | Par

  | Num
  | Mul
  | Add

  | Key
  | Scr
  deriving (Generic, NFDataX, Eq, Show)

ancillaryPortCount :: Kind -> Index 3
ancillaryPortCount p = case p of
  Nan -> 0
  Rot -> 0
  Era -> 0
  Nul -> 0
  Key -> 0
  Scr -> 0
  Num -> 0
  Equ -> 1
  Abs -> 2
  App -> 2
  Dup -> 2
  Par -> 2
  Mul -> 2
  Add -> 2

data Pol = Pos | Neg deriving Eq

-- The polarity of the principal port of a node kind.
polarity :: Kind -> Pol
polarity p = case p of
  Nan -> undefined
  Equ -> undefined
  Nul -> Pos
  Abs -> Pos
  Par -> Pos
  Num -> Pos
  Key -> Pos
  Rot -> Neg
  Era -> Neg
  App -> Neg
  Dup -> Neg
  Mul -> Neg
  Add -> Neg
  Scr -> Neg

polarities :: Kind -> (Pol, Pol, Pol)
polarities p = case p of
  Nan -> (undefined, undefined, undefined)
  Equ -> (undefined, undefined, undefined)
  Nul -> (Pos, undefined, undefined)
  Abs -> (Pos, Neg, Pos)
  Par -> (Pos, Neg, Neg)
  Num -> (Pos, undefined, undefined)
  Key -> (Pos, undefined, undefined)
  Rot -> (Neg, undefined, undefined)
  Era -> (Neg, undefined, undefined)
  App -> (Neg, Pos, Neg)
  Dup -> (Neg, Pos, Pos)
  Mul -> (Neg, Pos, Neg)
  Add -> (Neg, Pos, Neg)
  Scr -> (Neg, undefined, undefined)


type Link n = (BitVector 2, Index (2 ^ n))

-- Convert a port to an index for index modification.
uidx :: KnownNat n => BitVector 2 -> Index n
uidx 0 = 0
uidx 1 = 1
uidx 2 = 2
uidx 3 = undefined

-- type LinkMemBits n = Unsigned (2 ^ n * 3 * (n + 2))
type LinkMemPorts n = Vec (2 ^ n * 3) (Link n)
type LinkMemNodes n = Vec (2 ^ n) (Vec 3 (Link n))

-- seperatePorts :: KnownNat n => LinkMemBits n -> LinkMemPorts n
-- seperatePorts = map (splitAt SNat) . unconcat SNat

--forgetPorts :: KnownNat n => LinkMemPorts n -> LinkMemBits n
--forgetPorts = concat . map (uncurry (++#))

seperateNodes :: KnownNat n => LinkMemPorts n -> LinkMemNodes n
seperateNodes = unconcat SNat

forgetNodes :: KnownNat n => LinkMemNodes n -> LinkMemPorts n
forgetNodes = concat

type Node n = (Kind, Vec 3 (Link n))
type Memory n = Vec (2 ^ n) (Node n)

unpackMemory :: KnownNat n => Memory n -> (Vec (2 ^ n) Kind, LinkMemNodes n)
unpackMemory = unzip

packMemory :: KnownNat n => (Vec (2 ^ n) Kind, LinkMemNodes n) -> Memory n
packMemory = uncurry zip

type NumFormat n = BitVector (2 * n + 4)

numFormat :: (KnownNat n) => NumFormat n -> (Link n, Link n)
numFormat = bitCoerce

numUnformat :: (KnownNat n) => (Link n, Link n) -> NumFormat n
numUnformat = bitCoerce

-- No operation for kind scattering
noopK :: forall n m . (KnownNat n, KnownNat m) => Vec n (Index m, Kind)
noopK = repeat (maxBound, Nan)

-- No operation for link scattering
noopL :: forall n m . (KnownNat n, KnownNat m) => Vec n (Index (2 ^ m * 3 + 1), Link m)
noopL = repeat (maxBound, (0, 0))

noopEq :: forall n m . (KnownNat n, KnownNat m) => Vec n (Link m, Link m)
noopEq = repeat ((0, 0), (0, 0))

-- Note: Abs isn't a duplicator for Scr, Add, or Mul and App isn't a duplicator for Key or Num
--       since they can't reverse their polarities.
duplicationCheck x y =
  let con x y =
        (x == Era && y == Par) ||
        ((x == Era || x == Dup) && (y == Abs || y == Nul || y == Key || y == Num)) ||
        ((x == Add || x == Mul || x == Scr || x == App) && (y == Par || y == Nul))
  in con x y || con y x

reverseEraser Nul = Era
reverseEraser Era = Nul
reverseEraser _ = undefined

reverseDuplicator Dup = Par
reverseDuplicator Par = Dup
reverseDuplicator Abs = App
reverseDuplicator App = Abs
reverseDuplicator _ = undefined

-- Generates the scattering pattern of a duplication.
-- Note that it's assumed that both ports interacting has
-- already been verified.
duplicationInstructions :: KnownNat n
  => Maybe (Index (2 ^ n))
  -> Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), Link n))
duplicationInstructions e (x, (xs0, xa0) :> x1 :> x2 :> Nil)
                          (y, (ys0, ya0) :> y1 :> y2 :> Nil) =
  case (polarities x, ancillaryPortCount x, polarities y, ancillaryPortCount y) of
    -- Two competing erasers delete themselves.
    ((Pos, _, _), 0, (Neg, _, _), 0) ->
      ((resize ya0, Nan) :> noopK, noopL)
    ((Neg, _, _), 0, (Pos, _, _), 0) ->
      ((resize ya0, Nan) :> noopK, noopL)

    -- Other than Eq, there are no tunnels, so this generic logic isn't needed.
    {-
    -- An eraser meeting a tunnel passes through it;
    ((Pos, _, _), 0, (Neg, p, _), 1) ->
      (\a -> (a :> noopK, ((3* resize ya0), y1) :> noopL)) $ case p of
        Pos -> (maxBound, Nan)
        Neg -> (resize ya0, reverseEraser x)
    ((Neg, _, _), 0, (Pos, p, _), 1) ->
      (\a -> (a :> noopK, ((3* resize ya0), y1) :> noopL)) $ case p of
        Neg -> (maxBound, Nan)
        Pos -> (resize ya0, (reverseEraser x))
    -- The tunnel deletes itself.
    ((Neg, _, _), 1, (Pos, _, _), 0) ->
      ((resize ya0, Nan) :> noopK, noopL)
    ((Pos, _, _), 1, (Neg, _, _), 0) ->
      ((resize ya0, Nan) :> noopK, noopL)
    -}

    -- An eraser meeting a fork passes through its first ancillary port;
    ((Neg, _, _), 0, (Pos, p, _), 2) ->
      let a = case p of
                Neg -> (maxBound, Nan)
                Pos -> (resize ya0, reverseEraser x)
      in (a :> noopK, ((3* resize ya0), y1) :> noopL)
    ((Pos, _, _), 0, (Neg, p, _), 2) ->
      let a = case p of
                Pos -> (maxBound, Nan)
                Neg -> (resize ya0, reverseEraser x)
      in (a :> noopK, ((3* resize ya0), y1) :> noopL)
    -- The fork becomes a new eraser pointing at its second ancillary port.
    ((Neg, _, _), 2, (Pos, _, p), 0) ->
      let a = case p of
                Pos -> reverseEraser x
                Neg -> x
      in ((resize ya0, a) :> noopK, (3* resize ya0, y2) :> noopL)
    ((Pos, _, _), 2, (Neg, _, p), 0) ->
      let a = case p of
                Neg -> reverseEraser x
                Pos -> x
      in ((resize ya0, a) :> noopK, (3* resize ya0, y2) :> noopL)

    -- Other than Eq, there are no tunnels, so this generic logic isn't needed.
    {-
    -- An tunnel meeting a tunnel becomes a single tunnel
    ((Pos, _, _), 1, (Neg, p, _), 1) -> undefined
    -- The negative tunnel deletes itself.
    ((Neg, _, _), 1, (Pos, p, _), 1) -> undefined

    -- A tunnel meeting a fork should become two tunnels at the end of the fork.
    ((Pos, _, _), 1, (Neg, p, _), 2) -> undefined
    ((Neg, _, _), 1, (Pos, p, _), 2) -> undefined
    -- The fork should point at the new ends of the two tunnels.
    -- and the principal port should point at the old end.
    ((Neg, _, _), 2, (Pos, _, p), 1) -> undefined
    ((Pos, _, _), 2, (Neg, _, p), 1) -> undefined
    -}

    -- Both forks should turn into the positive fork.
    -- The new addresses will store the negative forks.
    -- The negative fork will create the second ancillary connections (including the node).
    ((Neg, _, p), 2, (Pos, _, q), 2) -> case e of
      Just j ->
        let a = case p of
                  Pos -> y
                  Neg -> reverseDuplicator y
            b = case q of
                  Neg -> x
                  Pos -> reverseDuplicator x
        in ((resize ya0, a) :> (resize j, b) :> noopK,
           (3* resize ya0, x2) :> (3* resize ya0 + 2, (2, j)) :>
           (3* resize j,   y2) :> (3* resize j + 1,   (2, xa0)) :> (3* resize j + 2, (2, ya0)) :>
           (3* resize xa0 + 2, (1, j)) :> noopL)
      Nothing -> (noopK, noopL)
    -- The positive fork will create the first anscilary connections (including the node).
    ((Pos, p, _), 2, (Neg, q, _), 2) -> case e of
      Just j ->
        let a = case q of
                  Pos -> x
                  Neg -> reverseDuplicator x
            b = case p of
                  Neg -> y
                  Pos -> reverseDuplicator y
        in ((resize ya0, a) :> (resize j, b) :> noopK,
           (3* resize ya0, y1) :> (3* resize ya0 + 1, (1, j)) :>
           (3* resize j,   x1) :> (3* resize j + 1,   (1, ya0)) :> (3* resize j + 2, (1, xa0)) :>
           (3* resize xa0 + 1, (2, j)) :> noopL)
      Nothing -> (noopK, noopL)

    (_, _, _, _) -> undefined

duplicationInstructionsLocal :: KnownNat n
  => Maybe (Index (2 ^ n))
  -> Node n
  -> Node n
  -> Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), Link n))
duplicationInstructionsLocal = undefined


duplicationInstructionsEq :: KnownNat n
  => Maybe (Index (2 ^ n))
  -> Node n
  -> Node n
  -> Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Link n, Link n) )
duplicationInstructionsEq mt
  (x, (xs0, xa0) :> (xs1, xa1) :> (xs2, xa2) :> Nil)
  (y, (ys0, ya0) :> y1 :> y2 :> Nil) 
  (a, a0 :> a1 :> a2 :> Nil)
  (b, b0 :> b1 :> b2 :> Nil) =
  undefined

annihilationCheck x y =
  let con x y =
        (x == App && y == Abs) ||
        (x == Dup && y == Par)
  in con x y || con y x

-- Generate scattering between an annihilation between
-- Two nodes with two anscilary ports.

-- Assumes annihilation check and proper connection
-- tests were already done.
{-
annihilationInstructions :: KnownNat n
  => Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), (Link n)))
annihilationInstructions (x, (xs0, xa0) :> x1 :> x2 :> Nil)
                         (y, (ys0, ya0) :> y1 :> y2 :> Nil) =
  let
    (a, b) = case (polarities x, polarities y) of
      -- The Positive case becomes an equation between the `1` ports.
      -- Equations should always have a negative principal port.
      ((Pos, Neg, _), (Neg, _, _)) -> (y1, x1)
      ((Pos, _, _), (Neg, Neg, _)) -> (x1, y1)
      -- The Negative case becomes an equation between the `2` ports
      ((Neg, _, Neg), (Pos, _, _)) -> (y2, x2)
      ((Neg, _, _), (Pos, _, Neg)) -> (x2, y2)
      ((_, _, _), (_, _, _)) -> undefined
  in
  ( (resize ya0, Equ) :> noopK
  , ((3* resize ya0), a) :> ((3* resize ya0 + 1), b) :> noopL)
-}

annihilationInstructions :: KnownNat n
  => Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), (Link n)))
annihilationInstructions (x, (xs0, xa0) :> (xs1, xa1) :> (xs2, xa2) :> Nil)
                         (y, (ys0, ya0) :> y1 :> y2 :> Nil) =
  let
    xs1' = case xs1 of
      0 -> 0
      1 -> 1
      2 -> 2
      3 -> undefined

    xs2' = case xs2 of
      0 -> 0
      1 -> 1
      2 -> 2
      3 -> undefined

  in ( (resize ya0, Nan) :> noopK
     , ((3* resize xa1 + xs1'), y1) :> ((3* resize xa2 + xs2'), y2) :> noopL)

annihilationInstructionsEq :: KnownNat n
  => Node n
  -> Node n
  -> Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Link n, Link n) )
annihilationInstructionsEq
  (x, (xs0, xa0) :> (xs1, xa1) :> (xs2, xa2) :> Nil)
  (y, (ys0, ya0) :> y1 :> y2 :> Nil) 
  (a, a0 :> a1 :> a2 :> Nil)
  (b, b0 :> b1 :> b2 :> Nil) =
  undefined

annihilationInstructionsLocal :: KnownNat n
  => Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), (Link n)) )
annihilationInstructionsLocal (x, (xs0, xa0) :> x1 :> x2 :> Nil)
                              (y, (ys0, ya0) :> y1 :> y2 :> Nil) = 
  let
    (a, b) = case (polarities x, polarities y) of
      -- The Positive case becomes an equation between the `1` ports.
      -- Equations should always have a negative principal port.
      ((Pos, Neg, _), (Neg, _, _)) -> (y1, x1)
      ((Pos, _, _), (Neg, Neg, _)) -> (x1, y1)
      -- The Negative case becomes an equation between the `2` ports
      ((Neg, _, Neg), (Pos, _, _)) -> (y2, x2)
      ((Neg, _, _), (Pos, _, Neg)) -> (x2, y2)
      ((_, _, _), (_, _, _)) -> undefined
  in
  ( (resize ya0, Equ) :> noopK
  , ((3* resize ya0), a) :> ((3* resize ya0 + 1), b) :> noopL )

data ALUInstructionHead = AddI | MulI

data ALUInstruction n
  = ALU { aluHead :: ALUInstructionHead
        , opAddr :: Index (2 ^ n)
        , arg1Addr :: Index (2 ^ n)
        , arg2Addr :: Index (2 ^ n) }

aluCheck x y =
  (x == Add || x == Mul) && (y == Num || y == Key)

aluInstructions :: KnownNat n
  => NumFormat n
  -> Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), (Link n))
     , Maybe (ALUInstruction n) )
aluInstructions key (x, (xs0, xa0) :> x1@(xs1, xa1) :> x2@(xs2, xa2) :> Nil)
               (y, (ys0, ya0) :> y1 :> y2 :> Nil) =
  let -- Keys must be converted into nums before being used.
      (keyKindI, keyInstr) =
        case y of
          Num -> (noopK, noopL)
          Key ->
            let (l1, l2) = numFormat key
            in ( (resize xa0, Num) :> Nil
               , ((3* resize xa0 + 1), l1) :> ((3* resize xa0 + 2), l2) :> Nil )
          _ -> undefined

  in case xs2 == 3 of
      True ->
        let head =
              case x of
                Mul -> MulI
                Add -> AddI
                _ -> undefined
        in ( (resize ya0, Num) :> (resize xa0, Nan) :> (resize xa2, Nan) :> noopK
           , (3* resize ya0, x1) :> (keyInstr ++ noopL)
           , Just $ ALU head ya0 xa0 xa2 )
      False ->
        ( keyKindI ++ noopK
        , (3* resize ya0 + 1, x2) :> (3* resize ya0 + 2, (3, xa1)) :> (keyInstr ++ noopL)
        , Nothing )

aluInstructionsLocal :: KnownNat n
  => NumFormat n
  -> Node n
  -> Node n
  -> Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), (Link n)) )
aluInstructionsLocal = undefined


aluInstructionsEq :: KnownNat n
  => NumFormat n
  -> Node n
  -> Node n
  -> Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Link n, Link n)
     , Maybe (ALUInstruction n) )
aluInstructionsEq = undefined


data ScreenInstruction numType
  = ScrI numType

screenCheck x y =
  (x == Scr) && (y == Num || y == Key)

screenInstructions :: KnownNat n
  => NumFormat n
  -> Index (2 ^ n)
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , ScreenInstruction (NumFormat n))
screenInstructions key xa0 (y, (ys0, ya0) :> y1 :> y2 :> Nil) =
  let val =
        case y of
          Key -> key
          Num -> numUnformat (y1, y2)
  in ( (resize xa0, Nan) :> (resize ya0, Nan) :> noopK
     , ScrI val )

generateInstructions :: (KnownNat n)
  => NumFormat n
  -> Maybe (Index (2 ^ n))
  -> Index (2 ^ n)
  -> Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), (Link n))
     , Maybe (ALUInstruction n)
     , Maybe (ScreenInstruction (NumFormat n)) )
generateInstructions key mt i
  n1@(x, (_, xa0) :> x1 :> _)
  n2@(y, (_, ya0) :> _) =
  case (x == Equ && y /= Equ, i == ya0, annihilationCheck x y, duplicationCheck x y, aluCheck x y, screenCheck x y) of
    (True, False, _, _, _, _) ->
          ( (resize i, Nan) :> noopK
          , ((3* resize xa0), x1) :> noopL
          , Nothing
          , Nothing)
    (False, False, _, _, _, _) -> (noopK, noopL, Nothing, Nothing)
    (_, _, True, _, _, _) ->
      let (a, b) = annihilationInstructions n1 n2
      in (a, b, Nothing, Nothing)
    (_, _, _, True, _, _) ->
      let (a, b) = duplicationInstructions mt n1 n2
      in (a, b, Nothing, Nothing)
    (_, _, _, _, True, _) ->
      let (a, b, c) = aluInstructions key n1 n2
      in (a, b, c, Nothing)
    (_, _, _, _, _, True) ->
      let (a, b) = screenInstructions key xa0 n2
      in (a, noopL, Nothing, Just b)

    (_, _, False, False, False, False) -> (noopK, noopL, Nothing, Nothing)

equInstructions :: (KnownNat n)
  => Node n
  -> Node n
  -> Bool
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), (Link n)) )
equInstructions = undefined

generateInstructionsEq :: (KnownNat n)
  => NumFormat n
  -> Maybe (Index (2 ^ n))
  -> Index (2 ^ n)
  -> Node n
  -> Node n
  -> Node n
  -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Link n, Link n)
     , Maybe (ALUInstruction n)
     , Maybe (ScreenInstruction (NumFormat n)) )
generateInstructionsEq key mt i
  n1@(x, (_, xa0) :> x1 :> _)
  n2@(y, (_, ya0) :> _) 
  a1 a2 =
  case (i == ya0, annihilationCheck x y, duplicationCheck x y, aluCheck x y, screenCheck x y) of
    (False, _, _, _, _) -> (noopK, noopEq, Nothing, Nothing)
    (_, True, _, _, _) ->
      let (a, b) = annihilationInstructionsEq n1 n2 a1 a2
      in (a, b, Nothing, Nothing)
    (_, _, True, _, _) ->
      let (a, b) = duplicationInstructionsEq mt n1 n2 a1 a2
      in (a, b, Nothing, Nothing)
    (_, _, _, True, _) ->
      let (a, b, c) = aluInstructionsEq key n1 n2 a1 a2
      in (a, b, c, Nothing)
    (_, _, _, _, True) ->
      let (a, b) = screenInstructions key xa0 n2
      in (a, noopEq, Nothing, Just b)

    (_, False, False, False, False) -> (noopK, noopEq, Nothing, Nothing)


generateInstructionsLocal :: (KnownNat n)
  => NumFormat n
  -> Maybe (Index (2 ^ n))
  -> Index (2 ^ n)
  -> Bool -> Bool -> Bool
  -> Node n
  -> Node n
  -> Bool -> Node n
  -> Bool -> Node n
  -> ( Vec 3 (Index (2 ^ n + 1), Kind)
     , Vec 6 (Index (2 ^ n * 3 + 1), (Link n))
     , Maybe (ScreenInstruction (NumFormat n)) )
generateInstructionsLocal key mt i
  isInteracting isDuplicating isAnnihilating
  n1@(x, (_, xa0) :> x1 :> _)
  n2@(y, (_, ya0) :> _) 
  isAnni1 a1 isAnni2 a2 =
  case (isInteracting, isDuplicating, isAnnihilating, aluCheck x y, screenCheck x y, x == Equ) of
    (_, _, _, _, _, True) ->
      let (a, b) = equInstructions n1 n2 isAnni1 a1
      in (a, b, Nothing)

    (False, _, _, _, _, False) -> (noopK, noopL, Nothing)
    (_, True, _, _, _, _) ->
      let (a, b) = duplicationInstructionsLocal mt n1 n2 a1 a2
      in (a, b, Nothing)
    (_, _, True, _, _, _) ->
      let (a, b) = annihilationInstructionsLocal n1 n2
      in (a, b, Nothing)
    (_, _, _, True, _, _) ->
      let (a, b) = aluInstructionsLocal key n1 n2 a1 a2
      in (a, b, Nothing)
    (_, _, _, _, True, _) ->
      let (a, b) = screenInstructions key xa0 n2
      in (a, noopL, Just b)

    (True, False, False, False, False, False) -> undefined -- (noopK, noopL, Nothing)
--    (_, _, _, _, _, _) -> (noopK, noopL, Nothing)

{-
Given a sparse memory with data randomly distributed, unknownGather will bubble the
nonempty values to the tp[, though it doesn't preserve order. This is useful for
gathering sparse data where the indexes of said data are unknown.

This creates a log-depth circuit.

DenseMem is an ordered pair consisting of, firstly, a vector which has dense data
followed by Nothing and, secondly, the index at which the Nothing starts.
-}
data DenseMem (a :: Type) (f :: TyFun Nat Type) :: Type
type instance Apply (DenseMem a) k = (Vec (2 ^ k) a, Index ((2 ^ k) + 1))

unknownGather' :: forall k a b . KnownNat k => (a -> Bool) -> (a -> b) -> b -> Vec (2 ^ k) a -> (Vec (2 ^ k) b, Index ((2 ^ k) + 1))
unknownGather' cond f def = dtfold (Proxy :: Proxy (DenseMem b)) base step where
  base a = case cond a of
    True -> (f a :> Nil, 1)
    False -> (def :> Nil, 0)

  denseMemFuse j vi vj = rotateRight (vi ++ reverse vj) j

  step :: SNat l -> DenseMem b @@ l -> DenseMem b @@ l -> DenseMem b @@ (l+1)
  step SNat (v1, i) (v2, j) = (denseMemFuse j v1 v2, resize i + resize j)

unknownGather :: forall k a b . KnownNat k => (a -> Bool) -> (a -> b) -> b -> Vec (2 ^ k) a -> Vec (2 ^ k) b
unknownGather cond f def = fst . unknownGather' cond f def

equationGather :: forall n . (KnownNat n)
  => Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n)), Index (3 * (2 ^ n))))
  -> Vec (3 * (2 ^ n)) (Vec 4 (Maybe (Index (3 * (2 ^ n)))))
equationGather eqs =
  let
    def :: Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n))))
    def = repeat Nothing

    valsL :: Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n))))
    valsR :: Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n))))
    (valsL, valsR) = unzip $ map (maybe (Nothing, Nothing) (\(i, j) -> (Just i, Just j))) eqs

    resL :: Vec (3 * (2 ^ n)) (Index (3 * (2 ^ n) + 1))
    resR :: Vec (3 * (2 ^ n)) (Index (3 * (2 ^ n) + 1))
    (resL, resR) = (map (maybe maxBound resize) valsL, map (maybe maxBound resize) valsR)

    -- Scatterings using both left and right index
    -- One scatters from the left and the other from the right.
    v1 :: Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n))))
    v2 :: Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n))))
    v3 :: Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n))))
    v4 :: Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n))))
    (v1, v2, v3, v4) =
      ( scatterWithGarbage def resL valsR
      , scatterWithGarbage def (reverse resL) (reverse valsR)
      , scatterWithGarbage def resR valsL
      , scatterWithGarbage def (reverse resR) (reverse valsL) )

  in transpose (v1 :> v2 :> v3 :> v4 :> Nil)

equationCombine1 :: forall n . (KnownNat n)
  => Index (3 * (2 ^ n))
  -> Maybe (Index (3 * (2 ^ n)))
  -> Maybe (Index (3 * (2 ^ n)))
  -> Maybe (Either (Index (3 * (2 ^ n))) (Index (3 * (2 ^ n)), Index (3 * (2 ^ n))))
equationCombine1 k Nothing Nothing = Nothing
equationCombine1 k (Just i) Nothing | k == i = Nothing 
                                    | True = Just $ Left i
equationCombine1 k Nothing (Just i) | k == i = Nothing 
                                    | True = Just $ Left i
equationCombine1 k (Just i) (Just j) =
  case (k == i, k == j) of
    (True, True) -> Nothing
    (True, False) -> Just $ Left j
    (False, True) -> Just $ Left i
    (False, False) -> case i == j of
      True -> Just $ Left i
      False -> Just $ Right (i, j)


equationCombine2 :: forall n . (KnownNat n)
  => Index (3 * (2 ^ n))
  -> Maybe (Either (Index (3 * (2 ^ n))) (Index (3 * (2 ^ n)), Index (3 * (2 ^ n))))
  -> Maybe (Either (Index (3 * (2 ^ n))) (Index (3 * (2 ^ n)), Index (3 * (2 ^ n))))
  -> Maybe (Index (3 * (2 ^ n)), Index (3 * (2 ^ n)))
equationCombine2 i Nothing Nothing = Nothing
equationCombine2 i (Just (Left j)) Nothing | i == j = Nothing
                                           | True = Just (i, j)
equationCombine2 i Nothing (Just (Left j)) | i == j = Nothing
                                           | True = Just (i, j)
equationCombine2 i (Just (Right p)) Nothing = Just p
equationCombine2 i Nothing (Just (Right p)) = Just p
equationCombine2 i (Just (Left j)) (Just (Left k)) | j == k = case k == i of
                                                       True -> Nothing
                                                       False -> Just (j, i)
                                                    | True = Just (j, k)
equationCombine2 _ (Just (Right (j, k))) (Just (Left l)) | j == l || j == k = Just (j, k)
                                                          | True = undefined
equationCombine2 _ (Just (Left l)) (Just (Right (j, k))) | j == l || j == k = Just (j, k)
                                                          | True = undefined
equationCombine2 _ (Just (Right (i, j))) (Just (Right (k, l))) =
  case (i==k&&j==l)||(i==l&&j==k) of
    True -> Just (i, j)
    False -> undefined

equationCombine :: forall n . (KnownNat n)
  => Index (3 * (2 ^ n))
  -> Vec 4 (Maybe (Index (3 * (2 ^ n))))
  -> (Maybe (Index (3 * (2 ^ n)), Index (3 * (2 ^ n))))
equationCombine i (a :> b :> c :> d :> Nil) =
  equationCombine2 i
    (equationCombine1 i a b)
    (equationCombine1 i c d)

equationTranitive :: forall n . (KnownNat n)
  => Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n)), Index (3 * (2 ^ n))))
  -> Vec (3 * (2 ^ n)) (Maybe (Index (3 * (2 ^ n)), Index (3 * (2 ^ n))))
equationTranitive = imap equationCombine . equationGather

equationTranitiveTestData :: 
  Vec (3 * (2 ^ 1)) (Maybe (Index (3 * (2 ^ 1)), Index (3 * (2 ^ 1))))
  =  Just (0, 1)
  :> Just (0, 2)
  :> Nothing
  :> Just (2, 4)
  :> Nothing
  :> Just (1, 5)
  :> Nil

{-
<
<<Just 2,Just 1,Nothing,Nothing>
,<Just 5,Just 5,Just 0,Just 0>
,<Just 4,Just 4,Just 0,Just 0>
,<Nothing,Nothing,Nothing,Nothing>
,<Nothing,Nothing,Just 2,Just 2>
,<Nothing,Nothing,Just 1,Just 1>>
-}

equationTranitiveTestData2 :: 
  Vec (3 * (2 ^ 1)) (Maybe (Index (3 * (2 ^ 1)), Index (3 * (2 ^ 1))))
  =  Just (0, 1)
  :> Just (0, 2)
  :> Just (3, 4)
  :> Just (2, 4)
  :> Just (3, 5)
  :> Nothing
  :> Nil

stepLocal :: forall n m r . (KnownNat n, KnownNat m, KnownNat r, (2 ^ n) ~ (m + r))
  => Memory n
  -> NumFormat n
  -> (Memory n, Vec m (Node n))
stepLocal mem key =
  let
    kmem :: Vec (2 ^ n) Kind
    lmem :: Vec (2 ^ n) (Vec 3 (Link n))
    (kmem, lmem) = unzip mem

    principalPairs :: Vec (2 ^ n) (Node n, Node n)
    principalPairs = zip mem $ gather mem (map (snd . head) lmem)

    conditions :: Index (2 ^ n) -> (Node n, Node n) -> ((Bool, Bool), Bool, Bool)
    conditions i ((x, _), (y, (_, ya0) :> _)) =
      let (b0, b1, b2) = (i == ya0, duplicationCheck x y, annihilationCheck x y)
      in ((b0, b1), b2, b0 && b1 && ancillaryPortCount x == 2 && ancillaryPortCount y == 2)

    instructionChecks :: Vec (2 ^ n) (Bool, Bool)
    annihilationChecks :: Vec (2 ^ n) Bool
    emptyNeedsChecks :: Vec (2 ^ n) Bool
    (instructionChecks, annihilationChecks, emptyNeedsChecks) = unzip3 $ imap conditions principalPairs

    memWithAnnihilationChecks :: Vec (2 ^ n) (Bool, Node n)
    memWithAnnihilationChecks = zip annihilationChecks mem

    localNodes :: Vec 3 (Vec (2 ^ n) (Bool, Node n))
    localNodes = map (gather memWithAnnihilationChecks) $ transpose $ map (map snd) lmem

    nodeNeighborhoods :: Vec (2 ^ n) (Vec 4 (Bool, Node n))
    nodeNeighborhoods = transpose (memWithAnnihilationChecks :> localNodes)


    isEmpty (x, _) = x == Nan

    emptyAddresses :: Vec (2 ^ n) (Maybe (Index (2 ^ n)))
    emptyAddresses = imap (\i (x, _) -> if x == Nan then Just i else Nothing) mem

    duplicationAddresses :: Vec (2 ^ n) (Maybe (Index (2 ^ n)))
    duplicationAddresses = imap (\i p -> if p then Just i else Nothing) emptyNeedsChecks

    gatheredEmptyAddresses :: Vec (2 ^ n) (Maybe (Index (2 ^ n)))
    gatheredDuplicationAddresses :: Vec (2 ^ n) (Index (2 ^ n + 1))
    (gatheredEmptyAddresses, gatheredDuplicationAddresses) = 
      ( unknownGather isJust id Nothing emptyAddresses
      , unknownGather isJust (\(Just i) -> resize i) maxBound duplicationAddresses )

    scatteredEmptyAddresses :: Vec (2 ^ n) (Maybe (Index (2 ^ n)))
    scatteredEmptyAddresses = scatterWithGarbage (repeat Nothing) gatheredDuplicationAddresses gatheredEmptyAddresses

    instructionalData :: Vec (2 ^ n) ( Maybe (Index (2 ^ n)), Bool, Bool, Bool
                                     , Node n, Node n, Bool, Node n, Bool, Node n)
    instructionalData = zipWith3 (\((an0, n1) :> (_, n2) :> (an1, a1) :> (an2, a2) :> Nil) 
                                   (intr, dup)
                                   mt ->
                                   (mt, intr, dup, an0, n1, n2, an1, a1, an2, a2)   )
                                 nodeNeighborhoods instructionChecks scatteredEmptyAddresses

    instructionsLocal :: Vec (2 ^ n)
                            ( Vec 3 (Index (2 ^ n + 1), Kind)
                            , Vec 6 (Index (2 ^ n * 3 + 1), Link n)
                            , Maybe (ScreenInstruction (NumFormat n)) )
    instructionsLocal = imap (\i (mt, intr, dup, an0, n1, n2, an1, a1, an2, a2) -> 
                               generateInstructionsLocal key mt i intr dup an0 n1 n2 an1 a1 an2 a2  )
                             instructionalData

    kindInstructions   :: Vec (2 ^ n) (Vec 3 (Index (2 ^ n + 1), Kind))
    linkInstructions   :: Vec (2 ^ n) (Vec 6 (Index (2 ^ n * 3 + 1), Link n))
    screenInstructions :: Vec (2 ^ n) (Maybe (ScreenInstruction (NumFormat n)))
    (kindInstructions, linkInstructions, screenInstructions) = unzip3 instructionsLocal

    -- aluInstructions    :: Vec (2 ^ n) (Maybe (ALUInstruction n))
    --((kindInstructions, linkInstructions), (aluInstructions, screenInstructions)) =
    --  bimap unzip unzip $ unzip $ map (\(a, b, c, d) -> ((a, b), (c, d))) instructionsLocal


    kindInstructions' :: (Vec ((2 ^ n) * 3) (Index (2 ^ n + 1)), Vec ((2 ^ n) * 3) Kind)
    kindInstructions' = unzip $ concat kindInstructions
    kmem' :: Vec (2 ^ n) Kind
    kmem' = uncurry (scatterWithGarbage kmem) kindInstructions'

    linkInstructions' :: (Vec ((2 ^ n) * 6) (Index (2 ^ n * 3 + 1)), Vec ((2 ^ n) * 6) (Link n))
    linkInstructions' = unzip $ concat linkInstructions
    lmem' :: Vec (2 ^ n * 3) (Link n)
    lmem' = uncurry (scatterWithGarbage (concat lmem)) linkInstructions'

    -- TO DO: Implement screen logic

    mem' :: Memory n
    mem' = zip kmem' (unconcat SNat $ lmem')

  in (mem', take SNat mem')

step :: forall n m r . (KnownNat n, KnownNat m, KnownNat r, (2 ^ n) ~ (m + r))
  => Memory n
  -> NumFormat n
  -> (Memory n, Vec m (Node n))
step mem key =
  let
    princIndex :: Node n -> Index (2 ^ n)
    princIndex (_, ((_, i) :> _)) = i

    -- Indexes of principal ports
    ppIndx :: Vec (2 ^ n) (Index (2 ^ n))
    ppIndx = map princIndex mem

    -- Nodes moved to wherever a principal port points to them
    sports :: Vec (2 ^ n) (Node n)
    sports = gather mem ppIndx

    -- Nodes paired up with whatever their principal ports point at.
    principalPairs :: Vec (2 ^ n) (Node n, Node n)
    principalPairs = zip mem sports

    isEmpty (x, _) = x == Nan

    emptyAddresses :: Vec (2 ^ n) (Maybe (Index (2 ^ n)))
    emptyAddresses = imap (\i (x, _) -> if x == Nan then Just i else Nothing) mem

    gatheredEmptyAddresses :: Vec (2 ^ n) (Maybe (Index (2 ^ n)))
    gatheredEmptyAddresses = unknownGather isJust id Nothing emptyAddresses

    duplicationCondition :: Index (2 ^ n) -> (Node n, Node n) -> Bool
    duplicationCondition i ((x, _), (y, (_, ya0) :> _)) =
      i == ya0 &&
      duplicationCheck x y &&
      ancillaryPortCount x == 2 &&
      ancillaryPortCount y == 2

    duplicationAddresses :: Vec (2 ^ n) (Maybe (Index (2 ^ n)))
    duplicationAddresses = imap (\i p -> if duplicationCondition i p then Just i else Nothing) principalPairs

    gatheredDuplicationAddresses :: Vec (2 ^ n) (Index (2 ^ n + 1))
    gatheredDuplicationAddresses = unknownGather isJust (\(Just i) -> resize i) maxBound duplicationAddresses

    scatteredEmptyAddresses :: Vec (2 ^ n) (Maybe (Index (2 ^ n)))
    scatteredEmptyAddresses = scatterWithGarbage (repeat Nothing) gatheredDuplicationAddresses gatheredEmptyAddresses

    instructions :: Vec (2 ^ n)
                        ( Vec 3 (Index (2 ^ n + 1), Kind)
                        , Vec 6 (Index (2 ^ n * 3 + 1), Link n)
                        , Maybe (ALUInstruction n)
                        , Maybe (ScreenInstruction (NumFormat n)) )
    instructions = izipWith (\i mt (n1, n2) -> generateInstructions key mt i n1 n2) scatteredEmptyAddresses principalPairs

    kindInstructions   :: Vec (2 ^ n) (Vec 3 (Index (2 ^ n + 1), Kind))
    linkInstructions   :: Vec (2 ^ n) (Vec 6 (Index (2 ^ n * 3 + 1), Link n))
    aluInstructions    :: Vec (2 ^ n) (Maybe (ALUInstruction n))
    screenInstructions :: Vec (2 ^ n) (Maybe (ScreenInstruction (NumFormat n)))
    ((kindInstructions, linkInstructions), (aluInstructions, screenInstructions)) =
      bimap unzip unzip $ unzip $ map (\(a, b, c, d) -> ((a, b), (c, d))) instructions

    kmem :: Vec (2 ^ n) Kind
    lmem :: Vec (2 ^ n) (Vec 3 (Link n))
    (kmem, lmem) = unzip mem

    kindInstructions' :: (Vec ((2 ^ n) * 3) (Index (2 ^ n + 1)), Vec ((2 ^ n) * 3) Kind)
    kindInstructions' = unzip $ concat kindInstructions
    kmem' :: Vec (2 ^ n) Kind
    kmem' = uncurry (scatterWithGarbage kmem) kindInstructions'

    linkInstructions' :: (Vec ((2 ^ n) * 6) (Index (2 ^ n * 3 + 1)), Vec ((2 ^ n) * 6) (Link n))
    linkInstructions' = unzip $ concat linkInstructions
    lmem' :: Vec (2 ^ n * 3) (Link n)
    lmem' = uncurry (scatterWithGarbage (concat lmem)) linkInstructions'

    lmemP :: Vec (2 ^ n) (Vec 3 (Link n))
    lmemP = unconcat SNat lmem'

    -- Arithmetic logic
    aluUnpack :: Maybe (ALUInstruction n)
              -> ( ( Maybe ALUInstructionHead
                   , (Maybe (Index (2 ^ n))) )
                 , ( Index (2 ^ n + 1)
                   , Index (2 ^ n + 1) )
                 )
    aluUnpack (Just (ALU hed tar arg1 arg2)) = ((Just hed, Just tar), (resize arg1, resize arg2))
    aluUnpack Nothing = ((Nothing, Nothing), (maxBound, maxBound))

    aluHeads   :: Vec (2 ^ n) (Maybe ALUInstructionHead)
    aluTargets :: Vec (2 ^ n) (Maybe (Index (2 ^ n)))
    aluArgs1   :: Vec (2 ^ n) (Index (2 ^ n + 1))
    aluArgs2   :: Vec (2 ^ n) (Index (2 ^ n + 1))
    ((aluHeads, aluTargets), (aluArgs1, aluArgs2)) = bimap unzip unzip $ unzip $ map aluUnpack aluInstructions

    aluNums1 :: Vec (2 ^ n) (NumFormat n)
    aluNums1 = map (\(_ :> x :> y :> Nil) -> numUnformat (x, y)) $ gather lmemP aluArgs1

    aluNums2 :: Vec (2 ^ n) (NumFormat n)
    aluNums2 = map (\(_ :> x :> y :> Nil) -> numUnformat (x, y)) $ gather lmemP aluArgs2

    aluLookup :: Maybe ALUInstructionHead -> (NumFormat n -> NumFormat n -> NumFormat n)
    aluLookup Nothing = const (const 0)
    aluLookup (Just h) = case h of
      AddI -> (+)
      MulI -> (*)

    aluResults :: Vec (2 ^ n) (NumFormat n)
    aluResults = zipWith3 aluLookup aluHeads aluNums1 aluNums2

    aluLinks :: Vec (2 ^ n * 2) (Link n)
    aluLinks = concat $ map ((\(a, b) -> a :> b :> Nil) . numFormat) aluResults

    aluTargetConv :: Maybe (Index (2 ^ n)) -> Vec 2 (Index (3 * 2 ^ n + 1))
    aluTargetConv Nothing = repeat maxBound
    aluTargetConv (Just i) = (3 * resize i + 1) :> (3 * resize i + 2) :> Nil

    aluTargetAddresses :: Vec (2 ^ n * 2) (Index (3 * 2 ^ n + 1))
    aluTargetAddresses = concat $ map aluTargetConv aluTargets

    lmem'' :: Vec (2 ^ n * 3) (Link n)
    lmem'' = scatterWithGarbage lmem' aluTargetAddresses aluLinks

    -- kmem'' :: Vec (2 ^ n) Kind
    -- kmem'' = scatterWithGarbage kmem' (aluArgs1 ++ aluArgs2) (repeat @(2 * (2 ^ n)) Nan)

    -- TO DO: Implement screen logic

    mem' :: Memory n
    mem' = zip kmem' (unconcat SNat $ lmem'')

  in (mem', take SNat mem')


-- Compiled from of `(\x -> x) (\x -> x)`
testMemory1 :: Vec (2 ^ 2) (Node 2)
testMemory1 =
  (Rot, (1, 1) :> (0, 0) :> (0, 0) :> Nil) :>
  (App, (0, 2) :> (0, 0) :> (0, 3) :> Nil) :>
  (Abs, (0, 1) :> (2, 2) :> (1, 2) :> Nil) :>
  (Abs, (2, 1) :> (2, 3) :> (1, 3) :> Nil) :>
  Nil

-- Compiled from of `(\x -> x) 23`
testMemory2 :: Vec (2 ^ 2) (Node 2)
testMemory2 =
  let (l1, l2) = numFormat 23
  in  (Rot, (1, 1) :> (0, 0) :> (0, 0) :> Nil) :>
      (App, (0, 2) :> (0, 0) :> (0, 3) :> Nil) :>
      (Abs, (0, 1) :> (2, 2) :> (1, 2) :> Nil) :>
      (Num, (2, 1) :> l1 :> l2 :> Nil) :>
      Nil

{-
Compiled from

(\f g x -> (x0, x1) = x -> f x0 (g x1))

-}
testMemory3 :: Vec (2 ^ 5) (Node 5)
testMemory3 =
  (Rot, (2, 1) :> (0, 0) :> (0, 0) :> Nil) :>
  (App, (2, 2) :> (0, 15) :> (0, 0) :> Nil) :> 
  (Abs, (2, 3) :> (0, 13) :> (0, 1) :> Nil) :> 
  (Abs, (0, 4) :> (0, 11) :> (0, 2) :> Nil) :> 
  (Abs, (0, 3) :> (0, 9) :> (0, 5) :> Nil) :> 
  (Abs, (2, 4) :> (0, 10) :> (0, 6) :> Nil) :> 
  (Abs, (2, 5) :> (0, 7) :> (2, 8) :> Nil) :> 
  (Dup, (1, 6) :> (1, 9) :> (1, 10) :> Nil) :> 
  (Abs, (2, 9) :> (2, 10) :> (2, 6) :> Nil) :> 
  (Abs, (1, 4) :> (1, 7) :> (0, 8) :> Nil) :> 
  (Abs, (1, 5) :> (2, 7) :> (1, 8) :> Nil) :> 
  (Abs, (1, 3) :> (2, 12) :> (0, 12) :> Nil) :> 
  (Abs, (2, 11) :> (1, 12) :> (1, 11) :> Nil) :> 
  (Abs, (1, 2) :> (2, 14) :> (0, 14) :> Nil) :> 
  (Abs, (2, 13) :> (0, 16) :> (1, 13) :> Nil) :> 
  (Abs, (1, 1) :> (2, 15) :> (1, 15) :> Nil) :> 
  (Era, (1, 14) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :>
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :>
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :>
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :>
  (Nan, (0, 0) :> (0, 0) :> (0, 0) :> Nil) :> 
  Nil


machine :: forall n m r dom . 
  (KnownNat n, KnownNat m, KnownNat r, (2 ^ n) ~ (m + r),

   KnownDomain dom,
   IP (HiddenClockName dom) (Clock dom),
   IP (HiddenEnableName dom) (Enable dom),
   IP (HiddenResetName dom) (Reset dom)) =>

   Memory n ->
   Signal dom (Vec m (Node n))
machine m =
  mealy step m (pure 0)

-- import qualified Data.List as L
-- sampleN 4 (machine testMemory1 :: Signal System (Vec 4 (Node 2)))