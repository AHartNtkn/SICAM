module Reduce where

import Data.Int

import Clash.Prelude
import Clash.Signal
import GHC.Classes

-- A pair of bits

data Int2 = I00 | I01 | I10 | I11 deriving (Generic, NFDataX, Eq, Show)

instance Num Int2 where 
  I00 + a = a
  a + I00 = a
  I01 + I01 = I10
  I01 + I10 = I11
  I01 + I11 = I00
  I10 + I01 = I11
  I10 + I11 = I01
  I11 + I11 = I10

  I00 * _ = I00
  _ * I00 = I00
  I01 * a = a
  a * I01 = a
  I10 * I10 = I00
  I10 * I11 = I10
  I11 * I10 = I10
  I11 * I11 = I01
  
  abs x = x

  signum I00 = I00
  signum _ = I01

  fromInteger x = go (mod x 4) where
    go m | m == 0 = I00
         | m == 1 = I01
         | m == 2 = I10
         | m == 3 = I11

  negate I00 = I00
  negate I01 = I11
  negate I10 = I10
  negate I11 = I01

-- 


{-
data Instruction n numType
  = Jump
  | Annihilate Int8 Int8
  | Duplicate Int8 Int8
  | Delete Int8
  | Literal Int8 numType
-}

-- Types characterizing the graph as layed out in memory.
type Port = Int2

type Link addr = (Port, addr)

data TernaryNode
  = Con
  | Dup
  | Add
  | Mul
  | Abs
  deriving (Generic, NFDataX, Eq, Show)

data UnitaryNode numType
  = Root
  | Del
  | Num numType
  deriving (Generic, NFDataX, Eq, Show)

data Node addr numType
  = Uni (UnitaryNode numType) (Link addr)
  | Ter TernaryNode (Link addr) (Link addr) (Link addr)
  deriving (Generic, NFDataX, Eq, Show)


data ALUInstruction
  = Add'
  | Multiply'
  | Absolute'

alu Add' x y = x + y
alu Multiply' x y = x * y
alu Absolute' x _ = abs x

data HeadInstruction addr
  = Warp'
  | Exit'
  | Backtrack' addr

-- Get the link on the other side of a link.
enter mem (port, addr) = 
  case mem !! addr of
    (True, _) -> undefined
    (False, n) -> case n of
      Ter _ l1 l2 l3 -> case port of
        I00 -> l1
        I01 -> l2
        I10 -> l3
        I11 -> undefined
      Uni _ l1 -> case port of
        I00 -> l1
        _ -> undefined

-- Insert a new node at the first empty address.
newNode mem n = findIndex fst mem >>= \i -> return $ replace i n mem

type ExitStack n numType = (numType, Vec n Port)
type ScheduleStack addr n numType = (numType, Vec n (Link addr))

proc :: (Num numType, Num schedulePointer, Num exitPointer
        ,KnownNat nm, KnownNat ns, KnownNat ne, KnownNat ni)
     => Vec nm (Bool, Node addr numType)
     -> (ScheduleStack addr ns schedulePointer
        ,ExitStack ne exitPointer
        ,Link addr)
     -> Vec ni numType
     -> ((ScheduleStack addr ns schedulePointer
         ,ExitStack ne exitPointer
         ,Link addr), 
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
