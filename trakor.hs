{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

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
  topCard :: a -> Card -- only needs to give correct value if validSet is True
  listCards   :: a -> [Card]

instance CardSet Card where
  validSet = const $ const True
  topCard = id
  listCards = (:[])


-- a set where every card has to be the same; ie pair, triple, etc
data EqSet a b = EqSet { fstEq :: a, sndEq :: b }
type Pair = EqSet Card Card
type Triple = EqSet Card Pair

instance (CardSet a, CardSet b) => CardSet (EqSet a b) where
  validSet ctx (EqSet x y) = validSet ctx x && validSet ctx y && topCard x == topCard y
  topCard = topCard . fstEq
  listCards x = (listCards $ fstEq x) ++ (listCards $ sndEq x)

compareSets :: (CardSet a) => a -> a -> CardContext -> Ordering
compareSets x y ctx = orderIf (validSet ctx x || validSet ctx y) $ (comparing (validSet ctx) x y) <> (compareOn (topCard x) (topCard y) ctx)

instance (CardSet a, CardSet b) => EqOn (EqSet a b) CardContext where
  (==.) a b c = compareSets a b c == EQ

instance (CardSet a, CardSet b) => OrdOn (EqSet a b) CardContext where
  compareOn = compareSets


-- a set where the top card of the left branch has to come immediately after the top card of the right branch;
--   ie tractors
data ConsecSet a b = ConsecSet { fstConsec :: a, sndConsec :: b }
type NormalTractor = ConsecSet Pair Pair

instance (CardSet a, CardSet b) => CardSet (ConsecSet a b) where
  validSet ctx (ConsecSet x y) = validSet ctx x && validSet ctx y && consecutiveCards ctx (topCard x) (topCard y)
  topCard = topCard . fstConsec
  listCards x = (listCards $ fstConsec x) ++ (listCards $ sndConsec x)

instance (CardSet a, CardSet b) => EqOn (ConsecSet a b) CardContext where
  (==.) a b c = compareSets a b c == EQ

instance (CardSet a, CardSet b) => OrdOn (ConsecSet a b) CardContext where
  compareOn = compareSets

-- (doesn't strictly need the Eq a, but I'm too lazy to implement this in a "better" way)
trickWinner :: (Eq a, CardSet a, OrdOn a CardContext) => Maybe Suit -> CardNum -> [a] -> Int
trickWinner tmpSuit tmpNum cards = fromJust $ elemIndex winner cards where
  firstPlay = head cards
  ctx = CardContext { firstSuit = cardSuit $ topCard firstPlay, trumpSuit = tmpSuit, trumpNum = tmpNum }
  winner = foldl (maxOfL ctx) firstPlay cards


main = return ()
