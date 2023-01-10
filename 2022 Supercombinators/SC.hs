module SC where

import Data.List
import Data.Maybe

import Types
import Examples

---------------------------------------------------------

prims :: [Id]
prims
  = ["+", "-", "*", "<=", "ite"]

lookUp :: Id -> [(Id, a)] -> a
lookUp v env
  = fromMaybe (error ("lookUp failed with search key " ++ v))
              (lookup v env)

---------------------------------------------------------
-- Part I

isFun :: Exp -> Bool
isFun (Fun _ _) = True
isFun _         = False

splitDefs :: [Binding] -> ([Binding], [Binding])
splitDefs = partition (isFun . snd)

topLevelFunctions :: Exp -> Int
topLevelFunctions (Let bs _)
  = length $ filter (isFun . snd) bs
topLevelFunctions _ = 0

---------------------------------------------------------
-- Part II

unionAll :: Eq a => [[a]] -> [a]
unionAll = nub . concat

freeVars :: Exp -> [Id]
freeVars (Const _)
  = []
freeVars (Var v)
  | v `elem` prims = []
  | otherwise      = [v]
freeVars (App f args)
  = unionAll (map freeVars (f:args))
freeVars (Fun params e)
  = (freeVars e) \\ params
freeVars (Let bs e)
  = freeVars e `union` unionAll (map (freeVars . snd) bs) \\ map fst bs

---------------------------------------------------------
-- Part III

-- Given...
lambdaLift :: Exp -> Exp
lambdaLift e
  = lift (modifyFunctions (buildFVMap e) e)

buildFVMap :: Exp -> [(Id, [Id])]
buildFVMap = sort . bfv'
  where
    bfv' (Let bs e)
      = fvs ++ concatMap bfv' (e : map snd bs)
      where
        (funs, _) = splitDefs bs
        funIds = map fst funs
        vs = sort $ unionAll [freeVars fe \\ funIds | (_, fe) <- funs]
        fvs = [(fId, vs) | (fId, _) <- funs]
    bfv' (Fun _ e)  = bfv' e
    bfv' (App e es) = concatMap bfv' (e:es)
    bfv' _ = []
    

modifyFunctions :: [(Id, [Id])] -> Exp -> Exp
-- Pre: The mapping table contains a binding for every function
-- named in the expression.
modifyFunctions fvmap (Let bs e) = Let (map mf' bs) (modifyFunctions fvmap e)
  where
    mf' (f, Fun as e)
      = ('$':f, Fun (lookUp f fvmap ++ as) (modifyFunctions fvmap e))
    mf' (v, e)
      = (v, modifyFunctions fvmap e)

modifyFunctions fvmap e@(Var f)
  | Just vs <- lookup f fvmap
    = if null vs
      then Var f'
      else App (Var f') (map Var vs)
  | otherwise = e
  where
    f' = '$':f

modifyFunctions fvmap (App f args)
  = App (modifyFunctions fvmap f) (map (modifyFunctions fvmap) args)

modifyFunctions _ e = e


-- The default definition here is id.
-- If you implement the above two functions but not this one
-- then lambdaLift above will remove all the free variables
-- in functions; it just won't do any lifting.
lift :: Exp -> Exp
lift e
  | null scs  = e'
  | otherwise = Let scs e'
  where
    (e', scs) = lift' e

-- You may wish to use this...
lift' :: Exp -> (Exp, [Supercombinator])
lift' (Let bs e)
  | null bsRes  = (e', supersRes)
  | otherwise   = (Let bsRes e', supersRes)
  where
    (e', scse)  = lift' e
    -- ([Id], [(Exp, [Supercombinator])])
    (vs, escss) = unzip $ map (\(b, e) -> (b, lift' e)) bs
    -- ([Exp], [[Supercombinator]])
    (es', scss) = unzip escss
    -- [Binding]
    bs' = zip vs es'
    (supers, bsRes) = splitDefs bs'

    supersRes = supers ++ scse ++ concat scss

lift' (Fun params e)
  = (Fun params e', scs)
  where
    (e', scs) = lift' e

lift' (App f args)
  = (App f' args', scsf ++ concat scssa)
  where
    (f', scsf) = lift' f
    (args', scssa) = unzip $ map lift' args

lift' e
  = (e, [])
