{-# LANGUAGE TupleSections, DataKinds, GADTs, KindSignatures #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-redundant-constraints #-}

{-# LANGUAGE NoImplicitPrelude #-}

-- stack exec --package clash-ghc -- clashi

module Main where

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

scatterWithGarbage :: forall k n m a . (KnownNat n, KnownNat m) =>
     Vec n a -> Vec m (Index (n + 1)) -> Vec (m + k) a -> Vec n a
scatterWithGarbage def idxs dat = init $ scatter (def ++ undefined :> Nil) idxs dat

data Racer (a :: Type) (f :: TyFun Nat Type) :: Type
type instance Apply (Racer a) k = Vec (k + 1) a -> Vec (k + 1) a -> Vec (k + 1) a


scatterRacersWithGarbage :: forall a l n m k . (KnownNat n, KnownNat m, KnownNat k, KnownNat l)
  => Vec n (Vec (l + 1) (Maybe a))
  -> Vec m (Index (n + 1))
  -> Vec (m + k) a
  -> Vec n (Vec (l + 1) (Maybe a))
scatterRacersWithGarbage def idxs dat = 
  let rc :: Vec (l + 1) (Maybe a) -> Vec (l + 1) (Maybe a) -> Vec (l + 1) (Maybe a)
      rc = dfold (Proxy :: Proxy (Racer (Maybe a))) rcS rc0 (repeat Nothing)

      rcS :: SNat o -> Maybe a -> Racer (Maybe a) @@ o -> Racer (Maybe a) @@ (o+1)
      rcS SNat k f (a :> l1) (b :> l2) = case (k, a, b) of
        (Nothing, Nothing, Nothing) -> Nothing :> f l1 l2
        _ -> undefined

      rc0 :: Racer (Maybe a) @@ 0
      rc0 (Just k :> Nil) (_ :> Nil) = (Just k :> Nil)
      rc0 (Nothing :> Nil) (k :> Nil) = (k :> Nil)   
  in init $ permute rc 
                    (def ++ (repeat Nothing :> Nil))
                    idxs 
                    (map (\x -> Just x :> repeat Nothing) dat)


scatter2RacersWithGarbage :: (KnownNat n, KnownNat m, KnownNat k)
  => Vec n (Vec 2 (Maybe a))
  -> Vec m (Index (n + 1))
  -> Vec (m + k) a
  -> Vec n (Vec 2 (Maybe a))
scatter2RacersWithGarbage def idxs dat =
  let rc :: Vec 2 (Maybe a) -> Vec 2 (Maybe a) -> Vec 2 (Maybe a)
      rc a@(Just k :> Just j :> Nil) _ = a
      rc (Just k :> Nothing :> Nil) (m :> _) = (Just k :> m :> Nil) 
      rc (Nothing :> Nothing :> Nil) b = b
      rc _ _ = undefined
  in init $ permute rc 
                    (def ++ ((Nothing :> Nothing :> Nil) :> Nil))
                    idxs 
                    (map (\x -> Just x :> Nothing :> Nil) dat)

scatter3RacersWithGarbage :: (KnownNat n, KnownNat m, KnownNat k)
  => Vec n (Vec 3 (Maybe a))
  -> Vec m (Index (n + 1))
  -> Vec (m + k) a
  -> Vec n (Vec 3 (Maybe a))
scatter3RacersWithGarbage def idxs dat =
  let rc :: Vec 3 (Maybe a) -> Vec 3 (Maybe a) -> Vec 3 (Maybe a)
      rc a@(Just _ :> Just _ :> Just _ :> Nil) _ = a
      rc (Just k :> Just j :> Nothing :> Nil) (m :> _) = (Just k :> Just j :> m :> Nil)
      rc (Just k :> Nothing :> Nothing :> Nil) (m :> n :> _) = (Just k :> m :> n :> Nil) 
      rc (Nothing :> Nothing :> Nothing :> Nil) b = b
      rc _ _ = undefined
  in init $ permute rc 
                    (def ++ (repeat Nothing :> Nil))
                    idxs 
                    (map (\x -> Just x :> repeat Nothing) dat)

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

unknownGather' :: forall k a b . KnownNat k 
               => (a -> Bool) 
               -> (a -> b) 
               -> b 
               -> Vec (2 ^ k) a 
               -> ( Vec (2 ^ k) b
                  , Index ((2 ^ k) + 1) )
unknownGather' cond f def = dtfold (Proxy :: Proxy (DenseMem b)) base step where
  base a = case cond a of
    True -> (f a :> Nil, 1)
    False -> (def :> Nil, 0)

  denseMemFuse j vi vj = rotateRight (vi ++ reverse vj) j

  step :: SNat l -> DenseMem b @@ l -> DenseMem b @@ l -> DenseMem b @@ (l+1)
  step SNat (v1, i) (v2, j) = (denseMemFuse j v1 v2, resize i + resize j)

unknownGather :: forall k a b . KnownNat k 
              => (a -> Bool) 
              -> (a -> b) 
              -> b 
              -> Vec (2 ^ k) a 
              -> Vec (2 ^ k) b
unknownGather cond f def = fst . unknownGather' cond f def


data ALUHead
  = Add
  | Mul
  deriving (Generic, NFDataX, Eq, Show)

data ALUState
  = Zero
  | One
  | Two
  deriving (Generic, NFDataX, Eq, Show)

data Kind
  = Equ
  | Rot

  | Era
  | Con
  | Dup

  | Num
  | Alu ALUHead Bool
  | If0 Bool

  | Key
  | Scr
  deriving (Generic, NFDataX, Eq, Show)

isAluKind (Alu _ _) = True
isAluKind _ = False

isIf0 (If0 _) = True
isIf0 _ = False

type NumFormat nam = BitVector (2 * nam)

numFormat :: (KnownNat nam) => NumFormat nam -> (Index (2 ^ nam), Index (2 ^ nam))
numFormat = bitCoerce

numUnformat :: (KnownNat nam) => (Index (2 ^ nam), Index (2 ^ nam)) -> NumFormat nam
numUnformat = bitCoerce

-- Bool indicates if the node is carrying data or addresses.
-- True for addresses, False for data.
type Node nam = (Kind, Index (2 ^ nam), (Bool, Vec 2 (Index (2 ^ nam))))
type Memory nam mem = Vec (2 ^ mem) (Maybe (Node nam))

unpackMemory :: forall nam mem . (KnownNat nam, KnownNat mem)
  => Memory nam mem
  -> ( Vec (2 ^ mem) (Maybe Kind)
     , Vec (2 ^ mem) (Maybe (Index (2 ^ nam)))
     , Vec (2 ^ mem) (Maybe (Bool, Vec 2 (Index (2 ^ nam)))) )
unpackMemory mem = 
  let mem' :: Vec (2 ^ mem) (Maybe Kind, Maybe (Index (2 ^ nam)), Maybe (Bool, Vec 2 (Index (2 ^ nam))))
      mem' = map (maybe (Nothing, Nothing, Nothing) (\(a, b, c) -> (Just a, Just b, Just c))) mem
  in unzip3 mem'

packMemory :: forall nam mem . (KnownNat nam, KnownNat mem)
  => ( Vec (2 ^ mem) (Maybe Kind)
     , Vec (2 ^ mem) (Maybe (Index (2 ^ nam)))
     , Vec (2 ^ mem) (Maybe (Bool, Vec 2 (Index (2 ^ nam)))) )
  -> Memory nam mem
packMemory (a, b, c) =
  let mem :: Vec (2 ^ mem) (Maybe Kind, Maybe (Index (2 ^ nam)), Maybe (Bool, Vec 2 (Index (2 ^ nam))))
      mem = zip3 a b c

      memProc :: (Maybe Kind, Maybe (Index (2 ^ nam)), Maybe (Bool, Vec 2 (Index (2 ^ nam))))
              -> Maybe (Kind, Index (2 ^ nam), (Bool, Vec 2 (Index (2 ^ nam))))
      memProc (Nothing, Nothing, Nothing) = Nothing
      memProc (Just a, Just b, Just c) = Just (a, b, c)
      memProc _ = undefined
  in map memProc mem

-- Permute memory so that all principal ports
-- are pointing to eachother.
interactingPorts :: forall nam mem . (KnownNat nam, KnownNat mem)
  => Memory nam mem
  -> Vec (2 ^ nam) (Vec 2 (Maybe (Node nam)))
interactingPorts mem = 
  let memMap n = maybe (maxBound, Nothing) (\(k, a, b) -> (resize a, Just (k, a, b))) n

      scatter2RacersWithGarbageM :: (KnownNat n, KnownNat m, KnownNat k)
        => Vec n (Vec 2 (Maybe a))
        -> Vec m (Index (n + 1))
        -> Vec (m + k) (Maybe a)
        -> Vec n (Vec 2 (Maybe a))
      scatter2RacersWithGarbageM def idxs dat =
        let rc :: Vec 2 (Maybe a) -> Vec 2 (Maybe a) -> Vec 2 (Maybe a)
            rc a@(Just k :> Just j :> _) _ = a
            rc (Just k :> Nothing :> _) (m :> _) = (Just k :> m :> Nil) 
            rc (Nothing :> _) b = b
            rc _ _ = undefined
        in init $ permute rc 
                          (def ++ ((Nothing :> Nothing :> Nil) :> Nil))
                          idxs 
                          (map (:> Nothing :> Nil) dat)

  in uncurry (scatter2RacersWithGarbageM (repeat (repeat Nothing))) $ unzip $ map memMap mem

annihilationCheck x y = x == y

annihilationInteraction :: KnownNat nam
                        => Node nam 
                        -> Node nam 
                        -> Vec 2 (Maybe (Node nam))
annihilationInteraction 
  (k1, p1, (d1, a1 :> b1 :> Nil))
  (k2, p2, (d2, a2 :> b2 :> Nil)) = 
  case d1 of
    True -> Just (Equ, a2, (True, a1 :> 0 :> Nil)) :>
            Just (Equ, b2, (True, b1 :> 0 :> Nil)) :>
            Nil
    False -> repeat Nothing

duplicationCheck x y = 
  x == Era || 
  (x == Dup && y == Con) ||
  ((x == Dup || x == Con) && (y == Scr || y == Key || y == Num || y == Era || isAluKind y)) ||
  (x == Dup && isIf0 y)

duplicationInteraction :: KnownNat nam
  => Maybe (Vec 3 (Index (2 ^ nam)))
  -> Node nam
  -> Node nam
  -> Vec 4 (Maybe (Node nam))
duplicationInteraction mt
  (k1, p1, (d1, a1 :> b1 :> Nil))
  (k2, p2, (d2, a2 :> b2 :> Nil)) = 
  case (d1, d2) of
    (True, True) -> 
      case mt of
        Just (n1 :> n2 :> n3 :> Nil) -> 
          Just (k1, a2, (True, n1 :> p1 :> Nil)) :>
          Just (k1, b2, (True, n2 :> n3 :> Nil)) :>
          Just (k2, a1, (True, n1 :> n2 :> Nil)) :>
          Just (k2, b1, (True, p1 :> n3 :> Nil)) :>
          Nil
        Nothing -> undefined
    (True, False) ->
      Just (k2, a1, (False, a2 :> b2 :> Nil)) :>
      Just (k2, b1, (False, a2 :> b2 :> Nil)) :>
      repeat Nothing
    (False, True) ->
      Just (k1, a2, (False, a1 :> b1 :> Nil)) :>
      Just (k1, b2, (False, a1 :> b1 :> Nil)) :>
      repeat Nothing
    (False, False) -> repeat Nothing

equCheck x = x == Equ

equInteraction :: KnownNat nam
               => Node nam 
               -> Node nam 
               -> Vec 2 (Maybe (Node nam))
equInteraction 
  (k1, p1, (d1, a1 :> _ :> Nil))
  (k2, p2, ans) = 
  Just (k2, a1, ans) :> repeat Nothing

screenCheck x y = (x == Scr) && (y == Num || y == Key)

screenInteraction :: KnownNat nam
                  => Node nam 
                  -> Node nam 
                  -> Vec 2 (Maybe (Node nam))
screenInteraction 
  (k1, p1, (d1, a1 :> b1 :> Nil))
  (k2, p2, (d2, a2 :> b2 :> Nil)) = 
  undefined


aluCheck x y = 
 (isAluKind x && y == Num) ||
 (x == If0 False && y == Num) ||
 (x == If0 True && y == Con)

aluOp :: KnownNat nam
  => ALUHead
  -> NumFormat nam
  -> NumFormat nam
  -> NumFormat nam
aluOp h = case h of
  Add -> (+)
  Mul -> (*)

aluInteraction :: KnownNat nam
               => Node nam
               -> Node nam
               -> NumFormat nam
               -> ( Vec 2 (Maybe (Node nam))
                  , Maybe (Index (2 ^ nam)) )
aluInteraction 
  n1@(k, p1, (d1, a1 :> b1 :> Nil)) n2@(_, _, (_, a2 :> b2 :> _)) n = 
  case k of
    Alu h ast ->
      case ast of
        False -> ( Just (Alu h True, b1, (d1, a1 :> p1 :> Nil)) :>
                   Just n2 :>
                   Nil 
                 , Nothing )
        True  ->
          let m = numUnformat (a2, b2)
              (l1, l2) = numFormat (aluOp h n m)
          in ( Just (Num, a1, (False, l1 :> l2 :> Nil)) :>
               Nothing :>
               Nil
             , Just b1 )
    If0 ast -> 
      case ast of
        False -> ( Just (If0 True, b1, (d1, a1 :> p1 :> Nil)) :>
                   Just n2 :>
                   Nil 
                 , Nothing )
        True  -> (\(a, b) -> ( Just (Equ, a1, (True, a :> 0 :> Nil)) :>
                                Just (Era, b, (False, repeat 0)) :>
                                Nil
                              , Just b1) ) $
          case n == 0 of
            True -> (a2, b2)
            False -> (b2, a2)
    _ -> undefined

keyCheck x = x == Key

keyInteraction :: KnownNat nam
  => NumFormat nam 
  -> Node nam -> Node nam
  -> Vec 2 (Maybe (Node nam))
keyInteraction key
  (_, p1, _) n = 
  let (l1, l2) = numFormat key
  in Just (Num, p1, (False, l1 :> l2 :> Nil)) :>
     Just n :>
     Nil

interactionSwap :: Kind -> Kind -> Bool
interactionSwap k1 k2 = 
  k2 == Equ ||
  ((k1 == Scr || k1 == Key || k1 == Num || isAluKind k1) && 
   (k2 == Era || k2 == Dup || k2 == Con)) ||
  ((isAluKind k1 || k1 == Scr) && (k2 == Key)) ||
  (k1 == Num && isAluKind k2)

interaction :: forall nam . (KnownNat nam)
         => NumFormat nam 
         -> Maybe (Vec 3 (Index (2 ^ nam)))
         -> Vec 2 (Maybe (Node nam))
         -> NumFormat nam
         -> ( Vec 4 (Maybe (Node nam))
            , Maybe (Index (2 ^ nam)) )
interaction _ _ p@(_ :> Nothing :> Nil) _ = (p ++ repeat Nothing, Nothing)
interaction key mt p@(Just (a'@(x', _, _)) :> Just (b'@(y', _, _)) :> Nil) n =
  let
    (a, x, b, y) = if interactionSwap x' y'
                    then (b', y', a', x')
                    else (a', x', b', y')
  in
  if duplicationCheck x y
  then (duplicationInteraction mt a b, Nothing)

  else (\(x, y) -> (x ++ repeat Nothing, y)) $
    if equCheck x
    then (equInteraction a b, Nothing)

    else if annihilationCheck x y
    then (annihilationInteraction a b, Nothing)

    else if aluCheck x y
    then aluInteraction a b n

    else if keyCheck x
    then (keyInteraction key a b, Nothing)

    else if screenCheck x y
    then (screenInteraction a b, Nothing)

    else (p, Nothing)


-- Find all the equations and what they point to.
-- Update nodes with what equations assert should be there.
equationExecute :: forall nam mem . (KnownNat nam, KnownNat mem)
  => Memory nam mem
  -> Memory nam mem
equationExecute mem =
  let placementsMap1 :: Index (2 ^ mem) 
                     -> Node nam 
                     -> Maybe (Vec 2 (Index (2 ^ nam), (Index (2 ^ mem), Node nam)))
      placementsMap1 i n@(k, _, (d, a :> b :> Nil)) =
        if d
        then Just $ (a, (i, n)) :> (b, (i, n)) :> Nil
        else Nothing

      placementsMap2 :: Maybe (Vec 2 (Index (2 ^ nam), (Index (2 ^ mem), Node nam)))
                     -> Vec 2 (Index (2 ^ nam + 1), Maybe (Index (2 ^ mem), Node nam))
      placementsMap2 Nothing = repeat (maxBound, Nothing) 
      placementsMap2 (Just ((i, v) :> (j, u) :> Nil)) = (resize i, Just v) :> (resize j, Just u) :> Nil

      placements :: Vec (2 ^ mem) (Vec 2 (Index (2 ^ nam + 1), Maybe (Index (2 ^ mem), Node nam)))
      placements = imap (\i a -> placementsMap2 (a >>= placementsMap1 i)) mem

      imemMap :: Index (2 ^ mem)
              -> Maybe (Node nam)
              -> (Index (2 ^ nam + 1), Maybe (Index (2 ^ mem), Index (2 ^ nam)))
      imemMap i (Just (Equ, a, (_, b :> _))) = (resize a, Just (i, b))
      imemMap i _ = (maxBound, Nothing)

      eqInstrWith Nothing _ = Nothing
      eqInstrWith _ Nothing = Nothing
      eqInstrWith (Just (a, b)) (Just (c, d)) = Just (a, b, c, d)
  
      eqInstr :: Vec (2 ^ nam) (Maybe ( Index (2 ^ mem), Index (2 ^ nam)
                                       , Index (2 ^ mem), Node nam ))
      eqInstr = zipWith
                  eqInstrWith
                  (uncurry (scatterWithGarbage (repeat Nothing)) $ unzip $ imap imemMap mem)
                  (uncurry (scatterWithGarbage (repeat Nothing)) $ unzip $ concat $ placements)
      
      nodeMaker :: Index (2 ^ nam)
                -> Maybe (Index (2 ^ mem), Index (2 ^ nam), Index (2 ^ mem), Node nam)
                -> Vec 2 (Index (2 ^ mem + 1), Maybe (Node nam))
      nodeMaker _ Nothing = repeat (maxBound, Nothing)
      nodeMaker p (Just (ie, q, ib, (k, r, (d, a :> b :> Nil)))) =
        case k of
          Equ -> if q == r
                 then (resize ie, Nothing) :> (resize ib, Nothing) :> Nil
                 else repeat (maxBound, Nothing)
          _ -> (\(x, y) -> (resize ie, Nothing) :> 
                            (resize ib, Just (k, r, (d, x :> y :> Nil))) :> 
                            Nil) $
                case (p == a, p == b) of
                  (True, False) -> (q, b)
                  (False, True) -> (a, q)
                  _ -> undefined
  in uncurry (scatterWithGarbage mem) $ unzip $ concat $ imap nodeMaker eqInstr

gatherFreeNames ::
  forall nam mem thrd k . (KnownNat nam, KnownNat mem, KnownNat thrd, KnownNat k, (3 * thrd) ~ (2 ^ nam + k))
  => Memory nam mem
  -> Vec thrd (Vec 3 (Index (2 ^ nam)))
gatherFreeNames mem = 
  let ansMap :: (Bool, Vec 2 (Index (2 ^ nam))) 
             -> Vec 2 (Index (2 ^ nam + 1))
      ansMap (d, a :> b :> Nil) | d = resize a :> resize b :> Nil
                                | True = repeat maxBound

      princ :: Vec (2 ^ mem) (Index (2 ^ nam + 1))
      ans :: Vec (2 ^ mem) (Vec 2 (Index (2 ^ nam + 1)))
      (princ, ans) = unzip $ 
                     map (maybe (maxBound, repeat maxBound) 
                                (\(_, x, y) -> (resize x, ansMap y))
                         ) mem

      ans' :: Vec (2 * 2 ^ mem) (Index (2 ^ nam + 1))
      ans' = concat $ ans

      unams :: Vec (3 * 2 ^ mem) (Index (2 ^ nam + 1))
      unams = princ ++ ans'

      fnams :: Vec (2 ^ nam) (Maybe (Index (2 ^ nam)))
      fnams = scatterWithGarbage 
                (imap (\i _ -> Just i) (repeat Nothing))
                unams 
                (repeat @(3 * 2 ^ mem) Nothing)

      dnams :: Vec (2 ^ nam) (Index (2 ^ nam))
      dnams = unknownGather isJust (\(Just x) -> x) undefined fnams
  in unconcat SNat (dnams ++ repeat @k 0)

gatherDupLocations ::
  forall nam mem . (KnownNat nam)
  => Vec (2 ^ nam) (Vec 2 (Maybe (Node nam)))
  -> Vec (2 ^ nam) (Index (2 ^ nam + 1))
gatherDupLocations u =
  let isDup :: Vec 2 (Maybe (Node nam))
            -> Bool
      isDup (_ :> Nothing :> Nil) = False
      isDup (Just (k1, p1, (d1, _)) :> 
             Just (k2, p2, (d2, _)) :> Nil) =
        d1 && d2 && (duplicationCheck k1 k2 || duplicationCheck k2 k1)
      isDup _ = undefined
  in unknownGather (isDup . snd) (resize . fst) maxBound (imap (,) u)

scatterFreeNames ::
  forall k1 k2 nam mem thrd . 
  ( KnownNat nam
  , KnownNat mem
  , KnownNat thrd
  , KnownNat k1
  , KnownNat k2
  , (3 * thrd) ~ (2 ^ nam + k1)
  , (thrd + k2) ~ (2 ^ nam) )
  => SNat thrd
  -> Memory nam mem
  -> Vec (2 ^ nam) (Vec 2 (Maybe (Node nam)))
  -> Vec (2 ^ nam) (Maybe (Vec 3 (Index (2 ^ nam))))
scatterFreeNames _ mem ints = 
  let ansMap :: (Bool, Vec 2 (Index (2 ^ nam))) 
             -> Vec 2 (Index (2 ^ nam + 1))
      ansMap (d, a :> b :> Nil) | d = resize a :> resize b :> Nil
                                | True = repeat maxBound

      princ :: Vec (2 ^ mem) (Index (2 ^ nam + 1))
      ans :: Vec (2 ^ mem) (Vec 2 (Index (2 ^ nam + 1)))
      (princ, ans) = unzip $ 
                     map (maybe (maxBound, repeat maxBound) 
                                (\(_, x, y) -> (resize x, ansMap y))
                         ) mem

      ans' :: Vec (2 * 2 ^ mem) (Index (2 ^ nam + 1))
      ans' = concat $ ans

      unams :: Vec (3 * 2 ^ mem) (Index (2 ^ nam + 1))
      unams = princ ++ ans'

      fnams :: Vec (2 ^ nam) (Maybe (Index (2 ^ nam)))
      fnams = scatterWithGarbage 
                (imap (\i _ -> Just i) (repeat Nothing))
                unams 
                (repeat @(3 * 2 ^ mem) Nothing)

      isDup :: Vec 2 (Maybe (Node nam))
            -> Bool
      isDup (_ :> Nothing :> Nil) = False
      isDup (Just (k1, p1, (d1, _)) :> 
             Just (k2, p2, (d2, _)) :> Nil) =
        d1 && d2 && (duplicationCheck k1 k2 || duplicationCheck k2 k1)
      isDup _ = undefined

      dnams :: Vec (2 ^ nam) (Maybe (Index (2 ^ nam)))
      ddups :: Vec (2 ^ nam) (Index (2 ^ nam + 1))
      (dnams, ddups) = 
        ( unknownGather isJust id Nothing fnams
        , unknownGather (isDup . snd) (resize . fst) maxBound (imap (,) ints) )

      dnams' :: Vec thrd (Vec 3 (Maybe (Index (2 ^ nam))))
      dnams' = unconcat SNat (dnams ++ repeat @k1 Nothing)

      dnamsMap :: Vec 3 (Maybe (Index (2 ^ nam)))
               -> Maybe (Vec 3 (Index (2 ^ nam)))
      dnamsMap (Nothing :> _) = Nothing
      dnamsMap (Just a :> Just b :> Just c :> Nil) =
        Just (a :> b :> c :> Nil)
      dnamsMap _ = undefined

      out :: Vec (2 ^ nam) (Maybe (Vec 3 (Index (2 ^ nam))))
      out = scatterWithGarbage (repeat Nothing) ddups (map dnamsMap dnams' ++ repeat @k2 Nothing)
  in out

aluExecute :: forall nam mem . (KnownNat nam, KnownNat mem)
  => Memory nam mem
  -> Memory nam mem
aluExecute = id

machineCycle :: forall k1 k2 n nam mem thrd . 
  ( KnownNat nam
  , KnownNat mem
  , KnownNat thrd
  , KnownNat k1
  , KnownNat k2
  , KnownNat n
  , (3 * thrd) ~ (2 ^ nam + k1)
  , (thrd + k2) ~ (2 ^ nam)
  , (2 ^ (nam + 2)) ~ ((2 ^ mem) + n)
  , (4 * 2 ^ nam) ~ (2 ^ (nam + 2))
  )
  => SNat thrd
  -> Memory nam mem
  -> NumFormat nam
  -> (Memory nam mem, Memory nam mem)
machineCycle n mem key = 
  let inter :: Vec (2 ^ nam) (Vec 2 (Maybe (Node nam)))
      inter = interactingPorts mem

      freeNames :: Vec (2 ^ nam) (Maybe (Vec 3 (Index (2 ^ nam))))
      freeNames = scatterFreeNames n mem inter

      sndPortsM :: Vec 2 (Maybe (Node nam))
                -> (NumFormat nam, Index (2 ^ nam))
      sndPortsM (p :> _) = case p of
        Nothing -> (0, 0)
        Just (_, _, (_, a :> b :> _)) -> (numUnformat (a, b), b)

      -- Gather all the numbers pointed to by a second ancillary port. 
      secondNums :: Vec (2 ^ nam) (NumFormat nam)
      secondNums = uncurry gather $ unzip $ map sndPortsM inter

      outMem' :: Vec (2 ^ nam) (Vec 4 (Maybe (Node nam)))
      usedNums :: Vec (2 ^ nam) (Maybe (Index (2 ^ nam)))
      (outMem', usedNums) = unzip $ zipWith3 (interaction key) freeNames inter secondNums

      outMem :: Vec (4 * 2 ^ nam) (Maybe (Node nam))
      outMem = concat $ scatterWithGarbage 
                            outMem' 
                            (map (maybe maxBound resize) usedNums)
                            (repeat @(2^nam) (repeat @4 Nothing))

      mem1 :: Memory nam mem
      mem1 = take SNat $ unknownGather isJust id Nothing outMem
      
      mem2 :: Memory nam mem
      mem2 = equationExecute mem1

      mem3 :: Memory nam mem
      mem3 = aluExecute mem2
  in (mem3, mem3)

machine :: forall k1 k2 n nam mem thrd dom . 
  ( KnownNat nam
  , KnownNat mem
  , KnownNat thrd
  , KnownNat k1
  , KnownNat k2
  , KnownNat n
  , (3 * thrd) ~ (2 ^ nam + k1)
  , (thrd + k2) ~ (2 ^ nam)
  , (2 ^ (nam + 2)) ~ ((2 ^ mem) + n)
  , (4 * 2 ^ nam) ~ (2 ^ (nam + 2))

  , KnownDomain dom
  , IP (HiddenClockName dom) (Clock dom)
  , IP (HiddenEnableName dom) (Enable dom)
  , IP (HiddenResetName dom) (Reset dom)
  ) => SNat thrd
  -> Memory nam mem
  -> Signal dom (Memory nam mem)
machine n m =
  mealy (machineCycle n) m (pure 0)


-- Compiled from `(\x -> x) (\x -> x)`
testMemory1 :: Memory 3 2
testMemory1 = map Just $
  (Rot, 1, (True, 0 :> 0 :> Nil)) :> -- 1 = Root
  (Con, 2, (True, 1 :> 3 :> Nil)) :> -- 1 = (2 3)
  (Con, 2, (True, 4 :> 4 :> Nil)) :> -- 2 = \4. 4
  (Con, 3, (True, 5 :> 5 :> Nil)) :> -- 3 = \5. 5
  Nil

-- sampleN 4 (machine (SNat :: SNat 3) testMemory1 :: Signal System (Memory 3 2))

-- Compiled from `(\x -> x) 23`
testMemory2 :: Memory 3 2
testMemory2 = map Just $
  let (l1, l2) = numFormat 23
  in  (Rot, 1, (True, 0 :> 0 :> Nil)) :>    -- 1 = Root
      (Con, 2, (True, 1 :> 3 :> Nil)) :>    -- 1 = (2 3)
      (Con, 2, (True, 4 :> 4 :> Nil)) :>    -- 2 = \4. 4
      (Num, 3, (False, l1 :> l2 :> Nil)) :> -- 3 = "23"
      Nil

{- Compiled from `S K K 23`

S = \f . \g . \x . f x (g x)

S = \f . u1
u1 = \g . u2
u2 = \x . u3
u3 = (u4 u5)
u4 = (f x)
u5 = (g x)

(Con, S,  (True, u1 :> f :>  Nil)) :> -- S = \f . u1
(Con, u1, (True, u2 :> g :>  Nil)) :> -- u1 = \g . u2
(Con, u2, (True, u3 :> x :>  Nil)) :> -- u2 = \x . u3
(Dup, x,  (True, x1 :> x2 :> Nil)) :> -- x = {x1, x2}
(Con, u4, (True, u3 :> u5 :> Nil)) :> -- u3 = (u4 u5)
(Con, f,  (True, u4 :> x1 :> Nil)) :> -- u4 = (f x1)
(Con, g,  (True, u5 :> x2 :> Nil)) :> -- u5 = (g x2)

K = \x. \y. x
(Con, K,  (True, u1 :> x :> Nil)) :> -- K = \x . u1
(Con, u1, (True, x  :> y :> Nil)) :> -- u1 = \y . x
(Era, y, (False, repeat 0)) :>       -- y = *

-}
testMemory3 :: Memory 6 5
testMemory3 = (\x -> map Just x ++ repeat Nothing) $
  let (l1, l2) = numFormat 23
  in  (Rot, 1, (True, 0 :> 0 :> Nil)) :>    -- 1 = Root

      (Con, 2, (True, 1 :> 3 :> Nil)) :>    -- 1 = (2 3)  ; SKKN = (SKK n)
      (Con, 4, (True, 2 :> 5 :> Nil)) :>    -- 2 = (4 5)  ; SKK = (SK K2)
      (Con, 6, (True, 4 :> 7 :> Nil)) :>    -- 4 = (6 7)  ; SK = (S K1)

      (Con, 6,  (True, 9  :> 8  :> Nil)) :> -- S = ...
      (Con, 9,  (True, 11 :> 10 :> Nil)) :>
      (Con, 11, (True, 13 :> 12 :> Nil)) :>
      (Dup, 12, (True, 14 :> 15 :> Nil)) :>
      (Con, 8,  (True, 16 :> 14 :> Nil)) :>
      (Con, 10, (True, 17 :> 15 :> Nil)) :>
      (Con, 16, (True, 13 :> 17 :> Nil)) :>

      (Con, 7,  (True, 19 :> 18 :> Nil)) :> -- K1 = ...
      (Con, 19, (True, 18 :> 20 :> Nil)) :>
      (Era, 20, (False, repeat 0)) :>

      (Con, 5,  (True, 22 :> 21 :> Nil)) :> -- K2 = ...
      (Con, 22, (True, 21 :> 23 :> Nil)) :>
      (Era, 23, (False, repeat 0)) :>

      (Num, 3, (False, l1 :> l2 :> Nil)) :> -- 3 = "23" ; n = 23
      Nil

-- sampleN 4 (machine (SNat :: SNat 22) testMemory3 :: Signal System (Memory 6 5))

-- Compiled from `K 5 10`
testMemory6 :: Memory 5 4
testMemory6 = (\x -> map Just x ++ repeat Nothing) $
  let (l1, l2) = numFormat 6
      (l3, l4) = numFormat 5
  in  (Rot, 1, (True, 0 :> 0 :> Nil)) :>    -- 1 = Root

      (Con, 2, (True, 1 :> 3 :> Nil)) :>    -- 1 = (2 3)  ; K21 = (K2 n1)
      (Con, 4, (True, 2 :> 5 :> Nil)) :>    -- 2 = (4 5)  ; K2 = (K n2)

      (Con, 4, (True, 7 :> 6 :> Nil)) :> -- K1 = ...
      (Con, 7, (True, 6 :> 8 :> Nil)) :>
      (Era, 8, (False, repeat 0)) :>

      (Num, 3, (False, l1 :> l2 :> Nil)) :>
      (Num, 5, (False, l3 :> l4 :> Nil)) :>
      Nil

-- sampleN 4 (machine (SNat :: SNat 11) testMemory6 :: Signal System (Memory 5 4))

testMemory4 :: Memory 4 3
testMemory4 = (\x -> map Just x ++ repeat Nothing) $
      (Rot, 1, (True, 0 :> 0 :> Nil)) :>    -- 1 = Root
      (Con, 2, (True, 1 :> 3 :> Nil)) :>    -- 1 = (2 3)
      (Dup, 4, (True, 2 :> 3 :> Nil)) :>    -- 4 = {2 3}
      (Con, 4, (True, 5 :> 5 :> Nil)) :>    -- 4 = \5 . 5
      Nil

-- sampleN 4 (machine (SNat :: SNat 6) testMemory4 :: Signal System (Memory 4 3))

testMemory7 :: Memory 4 3
testMemory7 = (\x -> map Just x ++ repeat Nothing) $
  let (l1, l2) = numFormat 5
      (l3, l4) = numFormat 7
  in  (Rot, 1, (True, 0 :> 0 :> Nil)) :>    -- 1 = Root

      (Alu Add False, 3, (True, 1 :> 2 :> Nil)) :>  -- 1 = 2 + 3 
      (Num, 2, (False, l1 :> l2 :> Nil)) :>         -- 2 = "5"
      (Num, 3, (False, l3 :> l4 :> Nil)) :>         -- 3 = "7"
      Nil

-- sampleN 10 (machine (SNat :: SNat 6) testMemory7 :: Signal System (Memory 4 3))
