{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Ord
import Data.Foldable
import Data.Maybe
import Data.List

orderIf :: Bool -> Ordering -> Ordering
orderIf True = id
orderIf False = const EQ

allSame :: (Eq a) => [a] -> Bool
allSame [] = True
allSame (h:r) = and $ map (== h) r

infix 4 ==.
infix 4 /=.
infix 4 <=.
infix 4 >=.
infix 4 <.
infix 4 >.

class EqOn a b where
  (==.) :: a -> a -> b -> Bool
  (/=.) :: a -> a -> b -> Bool
  x /=. y = not . (x ==. y)

class EqOn a b => OrdOn a b where
  compareOn :: a -> a -> b -> Ordering

  (<.)  :: a -> a -> b -> Bool
  (>.)  :: a -> a -> b -> Bool
  (>=.) :: a -> a -> b -> Bool
  (<=.) :: a -> a -> b -> Bool
  x <. y  = (== LT) . compareOn x y
  x >. y  = (== GT) . compareOn x y
  x >=. y = (/= LT) . compareOn x y
  x <=. y = (/= GT) . compareOn x y

  minOfL :: b -> a -> a -> a
  minOfR :: b -> a -> a -> a
  maxOfL :: b -> a -> a -> a
  maxOfR :: b -> a -> a -> a
  minOfL z x y
    | (x <=. y) z = x
    | otherwise   = y
  minOfR z x y
    | (x <. y) z  = x
    | otherwise   = y
  maxOfL z x y
    | (x >=. y) z = x
    | otherwise   = y
  maxOfR z x y
    | (x >. y) z  = x
    | otherwise   = y

data Suit = Diamond | Club | Heart | Spade deriving (Eq, Show)
type CardNum = Int
data Card = NormalCard { cardSuit :: Suit, cardNum :: CardNum } | Joker { bigJoker :: Bool } deriving (Eq, Show)
data CardContext = CardContext { firstSuit :: Suit, trumpSuit :: Maybe Suit, trumpNum :: CardNum } deriving (Eq, Show)

jack :: CardNum
jack = 11
queen :: CardNum
queen = 12
king :: CardNum
king = 13
ace :: CardNum
ace = 14

maybeSuit :: Card -> Maybe Suit
maybeSuit (Joker _) = Nothing
maybeSuit a = Just $ cardSuit a

maybeNum :: Card -> Maybe CardNum
maybeNum (Joker _) = Nothing
maybeNum a = Just $ cardNum a

applyToSuit :: a -> (Suit -> a) -> Card -> a
applyToSuit d f = maybe d f . maybeSuit

applyToNum :: a -> (CardNum -> a) -> Card -> a
applyToNum d f = maybe d f . maybeNum

isTrump :: CardContext -> Card -> Bool
isTrump ctx a = (applyToNum True (== trumpNum ctx) a) || (maybeSuit a == trumpSuit ctx)

-- 2 if big number, big suit; 1 if big number, not big suit; 0 otherwise
trumpNumValue :: CardContext -> Card -> Int
trumpNumValue _ (Joker _) = 0
trumpNumValue ctx card
  | trumpNum ctx /= cardNum card = 0
  | trumpSuit ctx /= Just (cardSuit card) = 1
  | otherwise = 2

-- 2 if trump suit; 1 if same suit as firstSuit; 0 otherwise
suitValue :: CardContext -> Card -> Int
suitValue ctx card
  | isTrump ctx card = 2
  | firstSuit ctx == cardSuit card = 1
  | otherwise = 0

-- first argument card comes AFTER second argument card, ie is greater than
consecutiveCards :: CardContext -> Card -> Card -> Bool
consecutiveCards _ (Joker a) (Joker b) = a > b
consecutiveCards _ (NormalCard _ _) (Joker _) = False
consecutiveCards ctx a@(Joker _) b@(NormalCard _ _) = not (bigJoker a) && trumpNumValue ctx b == 2
consecutiveCards ctx a@(NormalCard _ _) b@(NormalCard _ _)
  | tnv a == 2 = tnv b == 1
  | tnv a == 1 = isTrump ctx b && cardNum b == cardAt ace
  | otherwise = cardSuit a == cardSuit b && cardNum b == cardAt (cardNum a - 1)
  where
    tnv = trumpNumValue ctx
    cardAt n
      | n == trumpNum ctx = n-1
      | otherwise = n

numPoints :: Card -> CardNum
numPoints = applyToNum 0 f where
  f n
    | n == 5 = 5
    | n == 10 || n == king = 10

compareCards :: Card -> Card -> CardContext -> Ordering
compareCards (Joker _) (NormalCard _ _) _ = GT
compareCards (NormalCard _ _) (Joker _) _ = LT
compareCards (Joker a) (Joker b) _ = compare a b
compareCards a@(NormalCard _ _) b@(NormalCard _ _) ctx = orderIf notWorthless $ fold [c1,c2,c3] where
  c1 = comparing (suitValue ctx) a b
  c2 = comparing (trumpNumValue ctx) a b
  c3 = comparing cardNum a b
  notWorthless = suitValue ctx a /= 0 || suitValue ctx b /= 0

instance EqOn Card CardContext where
  (==.) a b c = compareCards a b c == EQ

instance OrdOn Card CardContext where
  compareOn = compareCards

-- ie, a thing that gets played (single card, pair, tractor, and so on)
class CardSet a where
  validSet :: CardContext -> a -> Bool
  highestCard :: a -> Card -- only needs to give correct value if validSet is True
  listCards   :: a -> [Card]

-- ie, a set of equivalent cards: pair, triple, and so on
-- every CardEqSet should be a CardSet but we don't do the (...) => ... thing
--   because we can auto derive CardSet from CardEqSet but not vice versa
class CardEqSet a where
  validEqSet :: a -> Bool
  eqSetCard  :: a -> Card -- only needs to give correct value if validEqSet is True
  listEqSetCards  :: a -> [Card]
  validEqSet = allSame . listCards

{-
instance (CardEqSet a) => CardSet a where
  validSet = const validEqSet
  highestCard = eqSetCard
  listCards = listEqSetCards
-}

instance CardEqSet Card where
  eqSetCard = id
  listEqSetCards = return

-- equal set append
data EqSetApp a = EqSetApp Card a
type Pair = EqSetApp Card
type Triple = EqSetApp Pair

instance (CardEqSet a) => CardEqSet (EqSetApp a) where
  eqSetCard (EqSetApp h _) = h
  listEqSetCards (EqSetApp h r) = h:(listCards r)

compareEqSetApps :: (CardEqSet a) => (EqSetApp a) -> (EqSetApp a) -> CardContext -> Ordering
compareEqSetApps x@(EqSetApp a _) y@(EqSetApp b _) ctx = orderIf (validEqSet x || validEqSet y) $ (comparing validEqSet x y) <> (compareOn a b ctx)

instance (CardEqSet a) => EqOn (EqSetApp a) CardContext where
  (==.) a b c = compareEqSetApps a b c == EQ

instance (CardEqSet a) => OrdOn (EqSetApp a) CardContext where
  compareOn = compareEqSetApps

data Tractor a b = Tractor a b
type NormalTractor = Tractor Pair Pair

instance (CardEqSet a, CardSet b) => CardSet (Tractor a b) where
  validSet c (Tractor x y) = validEqSet x && validSet c y && consecutiveCards c (highestCard x) (highestCard y)
  highestCard (Tractor x y) = highestCard x
  listCards (Tractor x y) = listCards x ++ listCards y

compareTractors :: (CardEqSet a, CardSet b) => Tractor a b -> Tractor a b -> CardContext -> Ordering
compareTractors x y ctx = orderIf (validEqSet x || validSet ctx y) $ (comparing (validSet ctx) x y) <> (compareOn (highestCard x) (highestCard y) ctx)

instance (CardEqSet a, CardSet b, EqOn a CardContext, EqOn b CardContext) => EqOn (Tractor a b) CardContext where
  (==.) a b c = compareTractors a b c == EQ

instance (CardEqSet a, CardSet b, OrdOn a CardContext, OrdOn b CardContext) => OrdOn (Tractor a b) CardContext where
  compareOn = compareTractors

-- (doesn't strictly need the Eq a, but I'm too lazy to implement this in a "better" way)
trickWinner :: (Eq a, CardSet a, OrdOn a CardContext) => Maybe Suit -> CardNum -> [a] -> Int
trickWinner tmpSuit tmpNum cards = fromJust $ elemIndex winner cards where
  firstPlay = head cards
  ctx = CardContext { firstSuit = cardSuit $ highestCard firstPlay, trumpSuit = tmpSuit, trumpNum = tmpNum }
  winner = foldl (maxOfL ctx) firstPlay cards



main = return ()
