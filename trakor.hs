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

firstNonEmpty :: [[a]] -> [a]
firstNonEmpty ([]:r) = firstNonEmpty r
firstNonEmpty (h:r) = h

removeFromList :: (Eq a) => [a] -> [a] -> [a]
removeFromList [] l = l
removeFromList (h:r) l = removeFromList r $ delete h l


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
data TrumpContext = TrumpContext { trumpSuit :: Maybe Suit, trumpNum :: CardNum } deriving (Eq, Show)
data CardContext = CardContext { firstSuit :: Maybe Suit, trumpCtx :: TrumpContext } deriving (Eq, Show)

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

maybeBig :: Card -> Maybe Bool
maybeBig (Joker a) = Just a
maybeBig _ = Nothing

applyToSuit :: a -> (Suit -> a) -> Card -> a
applyToSuit d f = maybe d f . maybeSuit

applyToNum :: a -> (CardNum -> a) -> Card -> a
applyToNum d f = maybe d f . maybeNum

applyToBig :: a -> (Bool -> a) -> Card -> a
applyToBig d f = maybe d f . maybeBig

isTrump :: TrumpContext -> Card -> Bool
isTrump ctx a = (applyToNum True (== trumpNum ctx) a) || (maybeSuit a == trumpSuit ctx)

firstCardTrump :: CardContext -> Bool
firstCardTrump ctx = firstSuit ctx == trumpSuit (trumpCtx ctx) || firstSuit ctx == Nothing

-- 2 if big number, big suit; 1 if big number, not big suit; 0 otherwise
trumpNumValue :: TrumpContext -> Card -> Int
trumpNumValue _ (Joker _) = 0
trumpNumValue ctx card
  | trumpNum ctx /= cardNum card = 0
  | trumpSuit ctx /= Just (cardSuit card) = 1
  | otherwise = 2

-- 1 if same suit as firstSuit (including trump); 2 if trump suit; 0 otherwise
suitValue :: CardContext -> Card -> Int
suitValue ctx card
  | isTrump (trumpCtx ctx) card = if (firstCardTrump ctx) then 1 else 2
  | firstSuit ctx == Just (cardSuit card) = 1
  | otherwise = 0

-- first argument card comes AFTER second argument card, ie is greater than
consecutiveCards :: TrumpContext -> Card -> Card -> Bool
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
compareCards a b ctx = orderIf notWorthless $ fold $ map (($ b) . ($ a)) $ [c0,c1,c2,c3] where
  c0 = comparing maybeBig
  c1 = comparing (suitValue ctx)
  c2 = comparing (trumpNumValue $ trumpCtx ctx)
  c3 = comparing maybeNum
  notWorthless = suitValue ctx a /= 0 || suitValue ctx b /= 0

instance EqOn Card CardContext where
  (==.) a b c = compareCards a b c == EQ

instance OrdOn Card CardContext where
  compareOn = compareCards


-- ie, a thing that gets played (single card, pair, tractor, and so on)
class CardSet a where
  validSet :: TrumpContext -> a -> Bool
  topCard :: a -> Card -- only needs to give correct value if validSet is True
  listCards :: a -> [Card]
  playableSets :: CardContext -> [Card] -> [a]

canPlayOn :: (CardSet a, Eq a) => CardContext -> [Card] -> a -> Bool
canPlayOn ctx hand play = elem play $ playableSets ctx hand

playableSingleCards :: CardContext -> [Card] -> [Card]
playableSingleCards ctx hand = firstNonEmpty [filter ((== 1) . suitValue ctx) hand, hand]

instance CardSet Card where
  validSet = const $ const True
  topCard = id
  listCards = (:[])
  playableSets = playableSingleCards


-- a set where every card has to be the same; ie pair, triple, etc
data EqSet b = EqSet { fstEq :: Card, sndEq :: b } deriving (Eq, Show)
type Pair = EqSet Card
type Triple = EqSet Pair

playableMultiSets :: (CardSet a, CardSet b, CardSet c) => (a -> b -> c) -> CardContext -> [Card] -> [c]
playableMultiSets constructor ctx hand = firstNonEmpty [filter (validSet $ trumpCtx ctx) sets, sets] where
  sets = do
    tailPart <- playableSets ctx hand
    headPart <- playableSets ctx $ removeFromList (listCards tailPart) hand
    return $ constructor headPart tailPart

instance (CardSet b) => CardSet (EqSet b) where
  validSet = const $ allSame . listCards
  -- validSet ctx (EqSet x y) = validSet ctx x && validSet ctx y && topCard x == topCard y
  topCard = topCard . fstEq
  listCards x = (listCards $ fstEq x) ++ (listCards $ sndEq x)
  playableSets = playableMultiSets EqSet -- TODO this makes it so you have to break triples

compareSets :: (CardSet a) => a -> a -> CardContext -> Ordering
compareSets x y ctx = orderIf (vstc x || vstc y) $ c0 <> c1 where
  c0 = comparing vstc x y
  c1 = compareOn (topCard x) (topCard y) ctx
  vstc = validSet (trumpCtx ctx)

instance (CardSet b) => EqOn (EqSet b) CardContext where
  (==.) a b c = compareSets a b c == EQ

instance (CardSet b) => OrdOn (EqSet b) CardContext where
  compareOn = compareSets


-- a set where the top card of the left branch has to come immediately after the top card of the right branch;
--   ie tractors
data ConsecSet a b = ConsecSet { fstConsec :: a, sndConsec :: b } deriving (Eq, Show)
type NormalTractor = ConsecSet Pair Pair

-- TODO: have to append things onto ConsecSet in the right order for this to work properly
--  something like EqSet : (EqSet : ...)

-- it does this correctly but note to future self: you *do* have to break up triple tractors if a normal tractor is played

instance (CardSet a, CardSet b) => CardSet (ConsecSet a b) where
  validSet ctx (ConsecSet x y) = validSet ctx x && validSet ctx y && consecutiveCards ctx (topCard x) (topCard y)
  topCard = topCard . fstConsec
  listCards x = (listCards $ fstConsec x) ++ (listCards $ sndConsec x)
  playableSets = playableMultiSets ConsecSet

instance (CardSet a, CardSet b) => EqOn (ConsecSet a b) CardContext where
  (==.) a b c = compareSets a b c == EQ

instance (CardSet a, CardSet b) => OrdOn (ConsecSet a b) CardContext where
  compareOn = compareSets

-- (doesn't strictly need the Eq a, but I'm too lazy to implement this in a "better" way)
trickWinner :: (Eq a, CardSet a, OrdOn a CardContext) => TrumpContext -> [a] -> Int
trickWinner trumpContext played = fromJust $ elemIndex winner played where
  firstPlay = head played
  ctx = CardContext { firstSuit = maybeSuit $ topCard firstPlay, trumpCtx = trumpContext }
  winner = foldl (maxOfL ctx) firstPlay played

validTrick :: (Eq a, CardSet a) => TrumpContext -> [[Card]] -> [a] -> Bool
validTrick trumpContext hands played = firstPlayValid && allPlaysValid where
  firstPlay = head played
  ctx = CardContext { firstSuit = maybeSuit $ topCard firstPlay, trumpCtx = trumpContext }
  firstPlayValid = validSet trumpContext firstPlay
  allPlaysValid = and $ map (uncurry $ canPlayOn ctx) $ zip hands played


main = return ()
