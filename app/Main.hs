{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}

module Main where

import Lib
import Prelude
import Data.Sort as Sort
import Data.HashSet as HashSet
import Data.HashMap.Strict as HashMap
import Data.Map as Map
import Language.HaLex.Dfa as Dfa
import Data.Hashable as Hashable
import GHC.Generics (Generic)
import Language.HaLex.Minimize as Min
import Language.HaLex.FaAsDiGraph as Viz


-- | A Recursive Data Structure to represent the regular expression 
data Regex  = Empty
            | Eps
            | CharSet (HashSet Char)
            | Not Regex
            | Star Regex
            | Intersect Regex Regex
            | Union Regex Regex
            | Dot Regex Regex
            deriving (Show, Generic, Ord, Eq)

data RegexSerial = Invalid 
                 | EndSerial
                 | SEmpty RegexSerial
                 | SEps RegexSerial
                 | SCharSet (HashSet Char) RegexSerial
                 | SNot RegexSerial
                 | SStar RegexSerial
                 | SIntersect RegexSerial
                 | SUnion RegexSerial
                 | SDot RegexSerial
                 deriving (Show, Ord, Eq)

data ConsumedInfo = ConsumedInfo (Maybe Regex) RegexSerial

data Attributes = Attributes Integer Integer Int
                | Default
                deriving (Show)

-- | Hashability is reguired to store unique states in a set
instance Hashable Regex

-- | Returns the size of a Regular expression. The empty expression (Empty), the empty string (Eps) and
-- any character set {x1, x2, ..., xn} is considered length 1. All operators contribute 1 to the length.
sizeRe:: Regex -> Int
sizeRe Empty = 1
sizeRe Eps = 1
sizeRe (CharSet _) = 1
sizeRe (Not r) = 1 + (sizeRe r)
sizeRe (Star r) = 1 + (sizeRe r)
sizeRe (Intersect r1 r2) = 1 + (sizeRe r1) + (sizeRe r2)
sizeRe (Union r1 r2) = 1 + (sizeRe r1) + (sizeRe r2)
sizeRe (Dot r1 r2) =  1 + (sizeRe r1) + (sizeRe r2)

-- | Returns 'Eps' if the expression is nullable, 'Empty' otherwise.
regexNullable:: Regex -> Regex
regexNullable r
    | (nullable r) == True = Eps
    | otherwise = Empty

-- | Returns 'True' if the expression nullable, 'False' otherwise.
nullable::Regex -> Bool
nullable Empty = False
nullable Eps = True
nullable (CharSet _) = False
nullable (Star _) = True
nullable (Not r) = not (nullable r)
nullable (Dot r1 r2) = (nullable r1) && (nullable r2)
nullable (Union r1 r2) = (nullable r1) || (nullable r2)
nullable (Intersect r1 r2) = (nullable r1) && (nullable r2)


-- | Computes the derivative of an expression with respect to a symbol.
deriv:: Regex -> Char -> Regex
deriv (CharSet cs) sy
    | HashSet.member sy cs = Eps
    | otherwise = Empty
deriv (Dot r1 r2) sy = {-Dot (deriv r1 sy) r2-} Union (Dot (deriv r1 sy) r2) (Dot (regexNullable r1) (deriv r2 sy))
deriv (Star r) sy = Dot (deriv r sy) (Star r)
deriv (Union r1 r2) sy = Union (deriv r1 sy) (deriv r2 sy)
deriv (Intersect r1 r2) sy = Intersect (deriv r1 sy) (deriv r2 sy)
deriv (Not r) sy = Not (deriv r sy)
deriv Empty _ = Empty
deriv Eps _ = Empty

-- | Simplifies a regex with an outer 'Union' operator.
simplifyUnion:: Regex -> Regex
simplifyUnion union = unpackUnionList (Sort.uniqueSort (simplifiedUnionList union))

-- | Creates a list from the operands of nested 'Union' operators.
simplifiedUnionList:: Regex -> [Regex]
simplifiedUnionList (Union r1 r2) = mergeUnionList (simplifiedUnionList r1) (simplifiedUnionList r2)
simplifiedUnionList r  =
    let sr = simplify r
    in if sr == r then [r] else simplifiedUnionList sr

-- | Simplies and merges two lists of nested 'Union' operands.
mergeUnionList:: [Regex] -> [Regex] -> [Regex]
mergeUnionList [Not Empty] _ = [Not Empty]
mergeUnionList _ [Not Empty] = [Not Empty]
mergeUnionList [Empty] lst = lst
mergeUnionList lst [Empty] = lst
mergeUnionList l1 l2 = l1 ++ l2

-- | Recompiles a simplified 'Union' list back to a regular expression with a standard format.
unpackUnionList:: [Regex] -> Regex
unpackUnionList [r] = r
unpackUnionList (r:rs) = Union r (unpackUnionList rs)

-- | Simplifies a regex with an outer 'Intersect' operator.
simplifyIntersect:: Regex -> Regex
simplifyIntersect intersect = unpackIntersectList (Sort.uniqueSort (simplifiedIntersectList intersect))

-- | Creates a list from the operands of nested 'Intersect' operators.
simplifiedIntersectList:: Regex -> [Regex]
simplifiedIntersectList (Intersect r1 r2) = mergeIntersectList (simplifiedIntersectList r1) (simplifiedIntersectList r2)
simplifiedIntersectList r = 
    let sr = simplify r
    in if sr == r then [r] else simplifiedIntersectList sr

-- | Simplies and merges two lists of nested 'Intersect' operands.
mergeIntersectList:: [Regex] -> [Regex] -> [Regex]
mergeIntersectList [Empty] _ = [Empty]
mergeIntersectList _ [Empty] = [Empty]
mergeIntersectList [Not Empty] lst = lst
mergeIntersectList lst [Not Empty] = lst
mergeIntersectList l1 l2 = l1 ++ l2

-- | Recompiles a simplified 'Intersect' list back to a regular expression with a standard format.
unpackIntersectList:: [Regex] -> Regex
unpackIntersectList [r] = r
unpackIntersectList (r:rs) = Intersect r (unpackIntersectList rs)

-- | Simplifies a regex with an outer 'Dot' operator.
simplifyDot:: Regex -> Regex
simplifyDot dot = unpackDotList $ simplifiedDotList dot

-- | Creates a list from the operands of nested 'Dot' operators.
simplifiedDotList:: Regex -> [Regex]
simplifiedDotList (Dot r1 r2) = mergeDotList (simplifiedDotList r1) (simplifiedDotList r2)
simplifiedDotList r =
    let sr = simplify r
    in if sr == r then [r] else simplifiedDotList sr

-- | Simplies and merges two lists of nested 'Dot' operands.
mergeDotList:: [Regex] -> [Regex] -> [Regex]
mergeDotList [Empty] _ = [Empty]
mergeDotList _ [Empty] = [Empty]
mergeDotList [Eps] lst = lst 
mergeDotList lst [Eps] = lst
mergeDotList l1 l2 = l1 ++ l2

-- | Recompiles a simplified 'Dot' list back to a regular expression with a standard format.
unpackDotList:: [Regex] -> Regex
unpackDotList [r] = r
unpackDotList (r:rs) = Dot r (unpackDotList rs)

-- | Simplifies a regular expression.
simplify:: Regex -> Regex
simplify (Union r1 r2) = simplifyUnion (Union r1 r2)
simplify (Intersect r1 r2) = simplifyIntersect (Intersect r1 r2)
simplify (Dot r1 r2) = simplifyDot (Dot r1 r2)
simplify (Not (Not r)) = simplify r
simplify (Star (Star r)) = simplify (Star r)
simplify (Star Eps) = Eps
simplify (Star Empty) = Eps
simplify (Star r) = Star (simplify r)
simplify (Not r) = Not (simplify r)
simplify r = r

-- | Check if a regex with an outer 'Union' operator is simplified
simplifiedUnion:: Regex -> Bool
simplifiedUnion (Union (Union _ _) _) = False
simplifiedUnion (Union Empty _) = False
simplifiedUnion (Union _ Empty) = False
simplifiedUnion (Union (Not Empty) _) = False
simplifiedUnion (Union _ (Not Empty)) = False
simplifiedUnion (Union r (Union s1 s2))
    | r < s1 = simplifiedUnion (Union s1 s2)
    | otherwise = False
simplifiedUnion (Union r s)
    | r < s = (simplified r) && (simplified s)
    | otherwise = False
simplifiedUnion r = simplified r

-- | Check if a regex with an outer 'Intersect' operator is simplified
simplifiedIntersect:: Regex -> Bool
simplifiedIntersect (Intersect (Intersect _ _) _) = False
simplifiedIntersect (Intersect Empty _) = False
simplifiedIntersect (Intersect _ Empty) = False
simplifiedIntersect (Intersect (Not Empty) _) = False
simplifiedIntersect (Intersect _ (Not Empty)) = False
simplifiedIntersect (Intersect r (Intersect s1 s2))
    | r < s1 = simplifiedIntersect (Intersect s1 s2)
    | otherwise = False
simplifiedIntersect (Intersect r s)
    | r < s = (simplified r) && (simplified s)
    | otherwise = False
simplifiedIntersect r = simplified r

-- | Check if a regex with an outer 'Dot' operator is simplified
simplifiedDot:: Regex -> Bool
simplifiedDot (Dot (Dot _ _) _) = False
simplifiedDot (Dot Empty _) = False
simplifiedDot (Dot _ Empty) = False
simplifiedDot (Dot Eps _) = False
simplifiedDot (Dot _ Eps) = False
simplifiedDot (Dot r s) = (simplified r) && (simplified s)
simplifiedDot r = simplified r

-- | Checks if a regular expression is simplified and in standard format
simplified:: Regex -> Bool
simplified (Union r s) = simplifiedUnion (Union r s)
simplified (Intersect r s) = simplifiedIntersect (Intersect r s)
simplified (Dot r s) = simplifiedDot (Dot r s)
simplified (Star (Star r)) = False
simplified (Not (Not r)) = False
simplified (Star Empty) = False
simplified (Star Eps) = False
simplified (Not r) = simplified r
simplified (Star r) = simplified r
simplified _ = True


-- A constructor for delta transition function using an underlying transition table and a 
-- default 'Regex' return in case a transition is absent in the table.
findTransition:: (HashMap Regex (HashMap Char Regex)) -> Regex -> Regex -> Char -> Regex
findTransition tt def inst sy = case (HashMap.lookup inst tt) of
    Nothing -> def
    Just trans -> case (HashMap.lookup sy trans) of
                    Nothing -> def
                    Just outst -> outst

-- | Constructs a DFA from a RE
constructDfa:: [Char] -> Regex -> (Dfa Regex Char)
constructDfa alph r = 
    let sr = simplify r
        tt = ttConstruct (HashMap.singleton sr (HashMap.empty)) alph alph sr
        fs = if
            | HashMap.member Eps tt -> [Eps]
            | otherwise -> []
        sts = HashMap.keys tt
    in Dfa alph sts sr fs (findTransition tt Empty)

-- | Constructs delta as a transposition table.
ttConstruct:: (HashMap Regex (HashMap Char Regex)) -> [Char] -> [Char] -> Regex -> (HashMap Regex (HashMap Char Regex))
ttConstruct tt alph [] r = tt
ttConstruct tt alph (x:xs) r =
    let sdr = simplify (deriv r x)
        tt1 = case (HashMap.lookup sdr tt) of
                Nothing -> ttConstruct (HashMap.insert sdr (HashMap.empty) (HashMap.adjust (HashMap.insert x sdr) r  tt)) alph alph sdr
                Just st -> HashMap.adjust (HashMap.insert x sdr) r  tt
    in ttConstruct tt1 alph xs r

-- | Returns true if a Dfa is minimal
isMinimalDfa::(Ord st, Eq sy) => Dfa st sy -> Bool
isMinimalDfa  dfa = Dfa.sizeDfa (Min.minimizeDfa dfa) == Dfa.sizeDfa dfa

-- | Slow check to see if a RE is simplified. The function does this by computing the simplified regex and comparing them.
isMinimalRe:: Regex -> Bool
isMinimalRe r = r == (simplify r)

-- | Creates a list of possible dissimilar combinations of two REs
mergeSingle:: Regex -> Regex -> [Regex]
mergeSingle r s
            | r == s = if
                | simplified (Dot r r) -> [Dot r r]
                | otherwise -> []
            | r <= s =
                let lst = if
                        | simplified (Union r s) -> [Union r s]
                        | otherwise -> []
                    lst2 = if
                        | simplified (Intersect r s) -> [Intersect r s] ++ lst
                        | otherwise -> lst
                    lst3 = if
                        | simplified (Dot s r) -> [Dot s r] ++ lst2
                        | otherwise -> lst2
                    lst4 = if
                        | simplified (Dot r s) -> [Dot r s] ++ lst3
                        | otherwise -> lst3
                in lst4
            | otherwise =  
                let lst = if
                        | simplified (Union s r) -> [Union s r]
                        | otherwise -> []
                    lst2 = if
                        | simplified (Intersect s r) -> [Intersect s r] ++ lst
                        | otherwise -> lst
                    lst3 = if
                        | simplified (Dot s r) -> [Dot s r] ++ lst2
                        | otherwise -> lst2
                    lst4 = if
                        | simplified (Dot r s) -> [Dot r s] ++ lst3
                        | otherwise -> lst3
                in lst4

-- | Creates a list of possible dissimilar REs created by applications of a univariate operator to 
-- the given RE.
applySingle2:: Regex -> [Regex] 
applySingle2 (Star r) = [Not (Star r)]
applySingle2 (Not r) = [Star (Not r)]
applySingle2 Eps = [Not Eps]
applySingle2 Empty = [Not Empty]
applySingle2 r = [Not r, Star r]

-- | Creates a list of all possible dissimilar REs created by combining a single RE with a list of REs,
-- Bounded by a maximum size.
mergeLeft:: Int -> Regex -> [Regex] -> [Regex]
mergeLeft l r (s:ss) 
    | (sizeRe r) + (sizeRe s) + 1 <= l = (mergeSingle r s) ++ (mergeLeft l r ss)
    | otherwise = mergeLeft l r ss
mergeLeft _ _ _ = []

-- | Creates a list of all possible dissimilar REs created by applying a list to itself,
-- with respect to both Binary and Unary operators, bounded by a maximum size.
mergeGrowNN:: Int -> [Regex] -> [Regex]
mergeGrowNN l (r:rs) = if
    | (sizeRe r) + 1 <= l -> (applySingle2 r) ++ (mergeLeft l r (r:rs)) ++ (mergeGrowNN l rs)
    | otherwise -> mergeGrowNN l rs
mergeGrowNN _ _ = []

-- | Creates a list of all possible dissimilar REs created by combining the elements from two lists,
-- with a Binary operator, bounded by a maximum size.
mergeGrowNO:: Int -> [Regex] -> [Regex] -> [Regex]
mergeGrowNO l (r:rs) lst = (mergeLeft l r lst) ++ (mergeGrowNO l rs lst)
mergeGrowNO _ _ _ = []

-- | Grows a list of dissimilar REs up to a given size recursively.
mergeGrow:: Int -> [Regex] -> [Regex] -> [Regex]
mergeGrow _ [] old = old
mergeGrow l new old = mergeGrow l ((mergeGrowNN l new) ++ (mergeGrowNO l new old)) (old ++ new)

-- | Grows a list of dissimilar REs up to the given size, using the elementary blocks:
--      - Empty
--      - Eps
--      - a
--      - b
--      - [a-b]
growDissimilarList:: Int -> [Regex]
growDissimilarList l = mergeGrow l [Empty, Eps, CharSet (HashSet.singleton 'a'), CharSet (HashSet.singleton 'b'), CharSet (HashSet.fromList "ab")] []

-- | Counts the amount of minimal DFAs constructed from a RE list, given some alphabet.
countMinimalDfas:: [Char] -> [Regex] -> Int
countMinimalDfas alph [] = 0
countMinimalDfas alph (r:rs)
    | isMinimalDfa (constructDfa alph r) = 1 + (countMinimalDfas alph rs)
    | otherwise = countMinimalDfas alph rs

-- | Prints all elements in list in their own line.
printElements:: (Show a) => [a] -> IO()
printElements = mapM_ print


-- | INTERNAL. Helper function for 'serialToRegex'
consumeRegexSerial:: RegexSerial -> ConsumedInfo
consumeRegexSerial (SEmpty ser) = ConsumedInfo (Just Empty) ser
consumeRegexSerial (SEps ser) = ConsumedInfo (Just Eps) ser
consumeRegexSerial (SCharSet hs ser) = ConsumedInfo (Just (CharSet hs)) ser
consumeRegexSerial EndSerial = ConsumedInfo Nothing EndSerial
consumeRegexSerial (SNot ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr) ser1 -> ConsumedInfo (Just (Not nr)) ser1
consumeRegexSerial (SStar ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr) ser1 -> ConsumedInfo (Just (Star nr)) ser1
consumeRegexSerial (SUnion ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr1) ser1 -> 
            case (consumeRegexSerial ser1) of 
                ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
                ConsumedInfo (Just nr2) ser2 -> ConsumedInfo (Just (Union nr1 nr2)) ser2
consumeRegexSerial (SIntersect ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr1) ser1 -> 
            case (consumeRegexSerial ser1) of 
                ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
                ConsumedInfo (Just nr2) ser2 -> ConsumedInfo (Just (Intersect nr1 nr2)) ser2
consumeRegexSerial (SDot ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr1) ser1 -> 
            case (consumeRegexSerial ser1) of 
                ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
                ConsumedInfo (Just nr2) ser2 -> ConsumedInfo (Just (Dot nr1 nr2)) ser2

-- | Turns a serialized RE into an RE, uses Maybe to accomodate invalid serial REs. 
serialToRegex:: RegexSerial -> (Maybe Regex)
serialToRegex ser =
    case (consumeRegexSerial ser) of
        ConsumedInfo (Just r) EndSerial -> (Just r)
        ConsumedInfo _ _ -> Nothing

-- | Ignore : Not Used 
countAttribute':: Int -> [HashSet Char] -> a -> (Regex -> a) -> (a -> a -> a) -> RegexSerial -> [HashSet Char] -> a
countAttribute' 0 _ idElem f g ser _ = case serialToRegex ser of
                Just r -> f r
                Nothing -> idElem
countAttribute' d alph idElem f g ser [] = 
    let a1 = case serialToRegex ser of
                Just r -> f r
                Nothing -> idElem
        dm1 = d - 1
        out =  ((g (countAttribute' dm1 alph idElem f g (SEmpty ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SEps ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SNot ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SStar ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SUnion ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SIntersect ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SDot ser) alph))) a1
    in out
countAttribute' d alph idElem f g ser (c:cs) = g (countAttribute' (d-1) alph idElem f g (SCharSet c ser) alph) (countAttribute' d alph idElem f g ser cs)

-- | Ignore: Not Used
countAttribute:: Int -> [HashSet Char] -> a -> (Regex -> a) -> (a -> a -> a) -> a
countAttribute d alph idElem f g = countAttribute' d alph idElem f g EndSerial alph

-- | INTERNAL: Helper function for 'growDisimilarListSerial'
growDissimilarListSerial':: Int -> [HashSet Char] -> [HashSet Char] -> RegexSerial -> ([Regex] -> [Regex])
growDissimilarListSerial' 0 _ _ ser = case serialToRegex ser of
    Just r -> if simplified r then ([r] ++) else ([] ++)
    Nothing -> ([] ++)
growDissimilarListSerial' d alph [] ser =
    let lst = case serialToRegex ser of
                Just r -> if simplified r then ([r] ++) else ([] ++)
                Nothing -> ([] ++)
        dm1 = d - 1
        out = lst
            . growDissimilarListSerial' dm1 alph alph (SEmpty ser)
            . growDissimilarListSerial' dm1 alph alph (SEps ser)
            . growDissimilarListSerial' dm1 alph alph (SNot ser)
            . growDissimilarListSerial' dm1 alph alph (SStar ser)
            . growDissimilarListSerial' dm1 alph alph (SUnion ser)
            . growDissimilarListSerial' dm1 alph alph (SIntersect ser)
            . growDissimilarListSerial' dm1 alph alph (SDot ser)
    in out
growDissimilarListSerial' d alph (c:cs) ser = (growDissimilarListSerial' (d - 1) alph alph (SCharSet c ser)) 
                                            . growDissimilarListSerial' d alph cs ser

-- | Grows a list of dissimlar REs using a serial RE construction method. Faster than 'growDisimilarList'.
growDissimilarListSerial :: Int -> [HashSet Char] -> [Regex]
growDissimilarListSerial d alph = (growDissimilarListSerial' d alph alph EndSerial) []

-- | Grows the same list as 'growDissimilarList' but faster, using the serial RE method.
growDissimilarListSerialAB :: Int -> [Regex]
growDissimilarListSerialAB d = growDissimilarListSerial d [HashSet.singleton 'a', HashSet.singleton 'b', HashSet.fromList "ab"]

-- | Ignore: Unused
getRegexAttributes:: Regex -> Attributes
getRegexAttributes r
    | simplified r = if
        | isMinimalDfa dfa -> Attributes 1 1 (sizeDfa dfa)
        | otherwise -> Attributes 1 0 0  
    | otherwise = Attributes 0 0 0
    where dfa = constructDfa "ab" r

-- | Ignore: Unused
mergeAttr:: Attributes -> Attributes -> Attributes
mergeAttr Default att = att
mergeAttr att Default = att
mergeAttr (Attributes dis1 min1 maxC1) (Attributes dis2 min2 maxC2) = Attributes (dis1 + dis2) (min1 + min2) (max maxC1 maxC2)

main :: IO ()
main = do
    let x = (CharSet $ HashSet.singleton 'a')
    let y = Not (Star (CharSet $ HashSet.singleton 'a'))
    let charRanges = [HashSet.singleton 'a', HashSet.singleton 'b', HashSet.fromList "ab"]
    let lst = growDissimilarListSerialAB 7 
    --print (serialToRegex (SUnion $ SEps $ SUnion $ SEmpty $ SEps $ SEps EndSerial))
    print (countAttribute 7 charRanges Default getRegexAttributes mergeAttr)
    --print (length lst)
    --printElements lst
    putStrLn ((show (length lst)) ++ "  " ++ (show (countMinimalDfas "ab" lst)))
    print (Union Eps Eps)
    print (simplify (
        Union Eps Eps) )