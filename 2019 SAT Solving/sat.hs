module SOL where

import Data.List
import Data.Maybe

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp x xys
  = fromJust $ lookup x xys

-- 3 marks
vars :: Formula -> [Id]
vars = nub . sort . vars'
  where
    vars' (Var v)   = [v]
    vars' (Not a)   = vars' a
    vars' (And a b) = vars' a ++ vars' b
    vars' (Or a b)  = vars' a ++ vars' b

-- 1 mark
idMap :: Formula -> IdMap
idMap = flip zip [1..] . vars

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF (Not (Or a b))  = And (toNNF (Not a)) (toNNF (Not b))
toNNF (Not (And a b)) = Or  (toNNF (Not a)) (toNNF (Not b))
toNNF (Not (Not a))   = toNNF a
toNNF f@(Var _)       = f
toNNF (Not a)         = Not (toNNF a)
toNNF (And a b)       = And (toNNF a) (toNNF b)
toNNF (Or a b)        = Or  (toNNF a) (toNNF b)


-- 3 marks
toCNF :: Formula -> CNF
toCNF = toCNF' . toNNF
  where
    toCNF' f@(Var _) = f
    toCNF' (Not a)   = Not (toCNF' a)
    toCNF' (And a b) = And (toCNF' a) (toCNF' b)
    toCNF' (Or  a b) = distribute a b

-- 4 marks
flatten :: CNF -> CNFRep
flatten f = flatten' f
  where
    idmap = idMap f

    flatten' (Var v)
      = [[lookUp v idmap]]
    flatten' (Not (Var v))
      = [[-(lookUp v idmap)]]
    flatten' (And a b)
      = flatten' a ++ flatten' b
    -- flatten' a and flatten' b guaranteed to be of form [[m,..,n]]
    -- as formula is in CNF 
    flatten' (Or a b)
      = [head (flatten' a) ++ head (flatten' b)]

--------------------------------------------------------------------------
-- Part III

isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _   = False

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits cs
  | null rest' = (cs, [])
  | otherwise  = (cs', u:us)
  where
    (first, rest') = break isSingleton cs
    ([u] : rest) = rest'

    csPropU = map (filter (/= (-u))) . filter (u `notElem`) $ first ++ rest

    (cs', us) = propUnits csPropU

-- 4 marks
dp :: CNFRep -> [[Int]]
dp cnf
  | null cnf'     = [us]
  | any null cnf' = []
  | otherwise     = map (us ++) (us1 ++ us2)
  where
    (cnf', us) = propUnits cnf

    n = head (head cnf')
    us1 = dp ([n]  : cnf')
    us2 = dp ([-n] : cnf')


--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat
  = undefined


