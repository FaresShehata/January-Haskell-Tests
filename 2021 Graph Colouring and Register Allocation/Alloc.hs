module Alloc where

import Data.Maybe
import Data.List
import Data.Function (on)

import Types
import Examples

------------------------------------------------------
--
-- Part I
--
count :: Eq a => a -> [a] -> Int
count x xs
  = foldl' (\s x' -> if x == x' then 1 + s else s) 0 xs


elemPair :: Eq a => a -> (a, a) -> Bool
x `elemPair` (y, z) = x == y || x == z

degrees :: Eq a => Graph a -> [(a, Int)]
degrees (labels, edges)
  = [(l, foldl' (\s p -> if l `elemPair` p then 1 + s else s) 0 edges)
    | l <- labels]


otherInPair :: Eq a => a -> (a, a) -> a
-- Pre: x is an element of the pair
otherInPair x (y, z)
  | x == y = z
  | x == z = y

neighbours :: Eq a => a -> Graph a -> [a]
neighbours n (_, edges)
  = [otherInPair n p | p <- edges, n `elemPair` p]


removeNode :: Eq a => a -> Graph a -> Graph a
removeNode n (labels, edges)
  = (filter (/= n) labels, filter (not . elemPair n) edges)

------------------------------------------------------
--
-- Part II
--
colourGraph :: (Ord a, Show a) => Int -> Graph a -> Colouring a
colourGraph numColours g@(labels, edges)
  | null labels = []
  | otherwise   = (n, c) : cMap
  where
    ((n, _) : _) = sortBy (compare `on` snd) (degrees g)

    cMap = colourGraph numColours (removeNode n g) -- [(a, Int)]

    neighboursOfn = neighbours n g
    coloursOfNeighbours = [c | (x, c) <- cMap, x `elem` neighboursOfn]

    availableColours = [1..numColours] \\ coloursOfNeighbours

    c = if null availableColours
        then 0
        else head availableColours

------------------------------------------------------
--
-- Part III
--
buildIdMap :: Colouring Id -> IdMap
buildIdMap vns = ("return", "return") : map b vns
  where
    b (v, 0) = (v, v)
    b (v, n) = (v, 'R' : show n)


buildArgAssignments :: [Id] -> IdMap -> [Statement]
buildArgAssignments args idmap
  = [Assign (lookUp a idmap) (Var a) | a <- args]


renameExp :: Exp -> IdMap -> Exp
-- Pre: A precondition is that every variable referenced in 
-- the expression is in the idMap. 
renameExp e@(Const _) _ = e
renameExp (Var v) idmap = Var (lookUp v idmap)
renameExp (Apply op e1 e2) idmap
  = Apply op (renameExp e1 idmap) (renameExp e2 idmap)


renameBlock :: Block -> IdMap -> Block
-- Pre: A precondition is that every variable referenced in 
-- the block is in the idMap. 
renameBlock [] _ = []
renameBlock ((Assign v e) : ss) idmap
  | Var v'' <- e', v' == v'' = renameBlock ss idmap
  | otherwise = Assign v' e' : renameBlock ss idmap
  where
    v' = lookUp v idmap
    e' = renameExp e idmap
renameBlock ((If e b1 b2) : ss) idmap
  = If (renameExp e idmap) (renameBlock b1 idmap) (renameBlock b2 idmap)
  : renameBlock ss idmap
renameBlock ((While e b) : ss) idmap
  = While (renameExp e idmap) (renameBlock b idmap)
  : renameBlock ss idmap


renameFun :: Function -> IdMap -> Function
renameFun (f, as, b) idMap
  = (f, as, buildArgAssignments as idMap ++ renameBlock b idMap)

-----------------------------------------------------
--
-- Part IV
--

buildIG :: [[Id]] -> IG
buildIG lvs = (nub . concat $ lvs, nub . concatMap b $ lvs)
  where
    b :: [Id] -> [Edge Id]
    b vs
     = [(x, y) | x <- vs, y <- vs, x < y]

-----------------------------------------------------
--
-- Part V
--

varsInExp :: Exp -> [Id]
varsInExp = nub . v'
  where
    v' (Const _)        = []
    v' (Var v)          = [v]
    v' (Apply op e1 e2) = v' e1 ++ v' e2

def :: ((Id, [Id]), [Int]) -> Id
def ((d, _), _) = d

use :: ((Id, [Id]), [Int]) -> [Id]
use ((_, u), _) = u

-- avoid name conflict
succ' :: ((Id, [Id]), [Int]) -> [Int]
succ' ((_, _), s) = s

-- Completed after 3 hours
liveVars :: CFG -> [[Id]]
liveVars duss = l' (map (const []) duss)
  where
    l' :: [[Id]] -> [[Id]]
    l' lives
      | lives' == lives = lives'
      | otherwise       = l' lives'
      where
        lives'
          = [use line `union`
             ((foldr union [] (map (lives !!) (succ' line)))
             \\ [def line])
            | line <- duss]


-- Completed after 3 hours
buildCFG :: Function -> CFG
-- Pre: Function is well formed, i.e.:
-- the first branch of an if statement is non empty
-- the body of a while loop is non empty and does not contain a return statement
-- a return statement is the last statement in a block or sub-block
buildCFG (_, _, b) = snd $ bcfg' 0 b
  where
    bcfg' :: Int -> Block -> (Int, CFG)
    bcfg' n [] = (n, [])
    bcfg' n ((Assign v e) : ss)
      = (n', ((v, varsInExp e), s) : cfg')
      where
        (n', cfg') = bcfg' (n + 1) ss

        s = if v == "return" then [] else [n + 1]

    bcfg' n ((If e b1 b2) : ss)
      = (n', (("_", varsInExp e), [n + 1, n1])
      : init cfg1 ++ (du, s')
      : cfg2 ++ cfg')
      where
        (n1, cfg1) = bcfg' (n + 1) b1
        (n2, cfg2) = bcfg' n1      b2
        (n', cfg') = bcfg' n2      ss

        (du, s) = last cfg1
        s' = if null s then s else [n2]

    bcfg' n ((While e b) : ss)
      = (n', (("_", varsInExp e), [n + 1, nb])
      : init cfgb ++ (du, [n]) : cfg')
      where
        (nb, cfgb) = bcfg' (n + 1) b
        (n', cfg') = bcfg' nb      ss
        (du, _) = last cfgb


transform :: Int -> Function -> Function
transform numRegisters f = renameFun f idmap
  where
    idmap = buildIdMap
          . colourGraph numRegisters
          . sortGraph
          . buildIG
          . liveVars
          . sortCFG
          . buildCFG $ f
