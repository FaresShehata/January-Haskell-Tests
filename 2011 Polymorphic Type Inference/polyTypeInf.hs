import Data.Maybe

data Expr = Number Int |
            Boolean Bool |
            Id String  |
            Prim String |
            Cond Expr Expr Expr |
            App Expr Expr |
            Fun String Expr
          deriving (Eq, Show)

data Type = TInt |
            TBool |
            TFun Type Type |
            TVar String |
            TErr 
          deriving (Eq, Show)

showT :: Type -> String
showT TInt  
  = "Int"
showT TBool 
  = "Bool"
showT (TFun t t') 
  = "(" ++ showT t ++ " -> " ++ showT t' ++ ")"
showT (TVar a) 
  = a
showT TErr  
  = "Type error"

type TypeTable = [(String, Type)]

type TEnv -- var, T
  = TypeTable    -- i.e. [(String, Type)]

type Sub -- TVar, T
  = TypeTable    -- i.e. [(String, Type)]  

-- Built-in function types...
primTypes :: TypeTable
primTypes 
  = [("+", TFun TInt (TFun TInt TInt)),
     (">", TFun TInt (TFun TInt TBool)),
     ("==", TFun TInt (TFun TInt TBool)),
     ("not", TFun TBool TBool)]

------------------------------------------------------
-- PART I

-- Pre: The search item is in the table
lookUp :: Eq a => a -> [(a, b)] -> b
lookUp x xys
  = fromJust $ lookup x xys

tryToLookUp :: Eq a => a -> b -> [(a, b)] -> b
tryToLookUp x y xys
  = fromMaybe y (lookup x xys)

-- Pre: The given value is in the table
reverseLookUp :: Eq b => b -> [(a, b)] -> [a]
reverseLookUp y xys
  = [x | (x, y') <- xys, y == y']

occurs :: String -> Type -> Bool
occurs s (TVar s') = s == s'
occurs s (TFun t1 t2) = occurs s t1 || occurs s t2
occurs _ _ = False

------------------------------------------------------
-- PART II

-- Pre: There are no user-defined functions (constructor Fun)
-- Pre: All variables in the expression have a binding in the given 
--      type environment
inferType :: Expr -> TEnv -> Type
inferType (Number _) _  = TInt
inferType (Boolean _) _ = TBool
inferType (Id v) env    = lookUp v env
inferType (Prim p) _    = lookUp p primTypes
inferType (Cond p e1 e2) env
  | inferType p env /= TBool = TErr
  | TErr `elem` [t1, t2]     = TErr
  | t1 /= t2                 = TErr
  | otherwise                = t1
  where
    t1 = inferType e1 env
    t2 = inferType e2 env
inferType (App f a) env
  = inferApp (inferType f env) (inferType a env)
  where
    inferApp :: Type -> Type -> Type
    inferApp (TFun t1 t2) t3
      | t1 == t3 = t2
    inferApp _ _ = TErr

------------------------------------------------------
-- PART III

applySub :: Sub -> Type -> Type
applySub s t@(TVar v) = tryToLookUp v t s
applySub s (TFun t1 t2) = TFun (applySub s t1) (applySub s t2)
applySub _ t = t

mapPair :: (a -> b) -> (a, a) -> (b, b)
mapPair f (x, y) = (f x, f y)


unify :: Type -> Type -> Maybe Sub
unify t t'
  = unifyPairs [(t, t')] []

unifyPairs :: [(Type, Type)] -> Sub -> Maybe Sub
unifyPairs [] s = Just s
unifyPairs ((TInt, TInt) : rest) s = unifyPairs rest s
unifyPairs ((TBool, TBool) : rest) s = unifyPairs rest s

unifyPairs ((TVar v, TVar v') : rest) s
  | v == v' = unifyPairs rest s

unifyPairs ((TVar v, t) : rest) s
  | occurs v t = Nothing
  | otherwise  = unifyPairs tts' s'
  where
    tts' = map (mapPair (applySub [(v, t)])) rest
    s' = (v, t) : s

unifyPairs ((t, t'@(TVar _)) : rest) s
  = unifyPairs ((t', t) : rest) s

unifyPairs ((TFun t1 t2, TFun t1' t2') : rest) s
  = unifyPairs ((t1, t1') : (t2, t2') : rest) s

unifyPairs _ _ = Nothing
------------------------------------------------------
-- PART IV

updateTEnv :: TEnv -> Sub -> TEnv
updateTEnv tenv tsub
  = map modify tenv
  where
    modify (v, t) = (v, applySub tsub t)

combine :: Sub -> Sub -> Sub
combine sNew sOld
  = sNew ++ updateTEnv sOld sNew

-- In combineSubs [s1, s2,..., sn], s1 should be the *most recent* substitution
-- and will be applied *last*
combineSubs :: [Sub] -> Sub
combineSubs 
  = foldr1 combine

inferPolyType :: Expr -> Type
inferPolyType e = applySub sub t
  where
    (sub, t, _) = ipt' e [] ['a' : show n | n <- [1..]]

-- BRO I HAVE NO IDEA
    ipt' :: Expr -> TEnv -> [String] -> (Sub, Type, [String])
    ipt' (Number _) _ as  = ([], TInt, as)
    ipt' (Boolean _) _ as = ([], TBool, as)
    ipt' (Prim p) _ as    = ([], lookUp p primTypes, as)
    ipt' e@(Id v) env aas@(a:as)
      | mte == Nothing = ([], TVar a, as)
      | otherwise      = ([], fromJust mte, aas)
      where
        mte = lookup v env

    ipt' (Fun x e) env (a:as)
      | te == TErr = ([], TErr, [])
      | otherwise = (sub, TFun tx te, as)
      where
        env' = (x, TVar a) : env
        (sub, te, as') = ipt' e env' as
        tx = applySub sub (TVar a)

    ipt' (App f e) env as
      | mSub == Nothing = ([], TErr, [])
      | otherwise = (sub', applySub uSub (TVar a), as')
      where
        (subf, tf, asf) = ipt' f env as
        (sube, te, (a:as')) = ipt' e (updateTEnv env subf) asf
        
        mSub = unify tf (TFun te (TVar a))
        uSub = fromJust mSub
        sub' = combineSubs [uSub, sube, subf]

    ipt' (Cond p e1 e2) env as
      | mSubp == Nothing = ([], TErr, [])
      | mSube == Nothing = ([], TErr, [])
      | otherwise = (sub', applySub uSube t1, as2)
      where
        (subp, tp', asp) = ipt' p env as
        mSubp = unify tp' TBool
        uSubp = fromJust mSubp

        env1 = updateTEnv env subp
        (sub1, t1, as1) = ipt' e1 env1 asp

        env2 = updateTEnv env1 sub1
        (sub2, t2, as2) = ipt' e2 env2 as1

        mSube = unify t1 t2
        uSube = fromJust mSube

        sub' = combineSubs [uSube, sub2, sub1, uSubp, subp]


------------------------------------------------------
-- Monomorphic type inference test cases from Table 1...

env :: TEnv
env = [("x",TInt),("y",TInt),("b",TBool),("c",TBool)]

ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8 :: Expr
type1, type2, type3, type4, type5, type6, type7, type8 :: Type

ex1 = Number 9
type1 = TInt

ex2 = Boolean False
type2 = TBool

ex3 = Prim "not"
type3 =  TFun TBool TBool

ex4 = App (Prim "not") (Boolean True)
type4 = TBool

ex5 = App (Prim ">") (Number 0)
type5 = TFun TInt TBool

ex6 = App (App (Prim "+") (Boolean True)) (Number 5)
type6 = TErr

ex7 = Cond (Boolean True) (Boolean False) (Id "c")
type7 = TBool

ex8 = Cond (App (Prim "==") (Number 4)) (Id "b") (Id "c")
type8 = TErr

------------------------------------------------------
-- Unification test cases from Table 2...

u1a, u1b, u2a, u2b, u3a, u3b, u4a, u4b, u5a, u5b, u6a, u6b :: Type
sub1, sub2, sub3, sub4, sub5, sub6 :: Maybe Sub

u1a = TFun (TVar "a") TInt
u1b = TVar "b"
sub1 = Just [("b",TFun (TVar "a") TInt)]

u2a = TFun TBool TBool
u2b = TFun TBool TBool
sub2 = Just []

u3a = TFun (TVar "a") TInt
u3b = TFun TBool TInt
sub3 = Just [("a",TBool)]

u4a = TBool
u4b = TFun TInt TBool
sub4 = Nothing

u5a = TFun (TVar "a") TInt
u5b = TFun TBool (TVar "b")
sub5 = Just [("b",TInt),("a",TBool)]

u6a = TFun (TVar "a") (TVar "a")
u6b = TVar "a"
sub6 = Nothing

------------------------------------------------------
-- Polymorphic type inference test cases from Table 3...

ex9, ex10, ex11, ex12, ex13, ex14, ex15 :: Expr
type9, type10, type11, type12, type13, type14 :: Type

ex9 = Fun "x" (Boolean True)
type9 = TFun (TVar "a1") TBool

ex10 = Fun "x" (Id "x")
type10 = TFun (TVar "a1") (TVar "a1")

ex11 = Fun "x" (App (Prim "not") (Id "x"))
type11 = TFun TBool TBool

ex12 = Fun "x" (Fun "y" (App (Id "y") (Id "x")))
type12 = TFun (TVar "a1") (TFun (TFun (TVar "a1") (TVar "a3")) (TVar "a3"))

ex13 = Fun "x" (Fun "y" (App (App (Id "y") (Id "x")) (Number 7)))
type13 = TFun (TVar "a1") (TFun (TFun (TVar "a1") (TFun TInt (TVar "a3"))) 
              (TVar "a3"))

ex14 = Fun "x" (Fun "y" (App (Id "x") (Prim "+"))) 
type14 = TFun (TFun (TFun TInt (TFun TInt TInt)) (TVar "a3")) 
              (TFun (TVar "a2") (TVar "a3"))

ex15 = Fun "x" (Fun "y" (Cond (App (App (Prim ">") (Id "x")) (Id "y"))
                              (Id "x")
                              (Id "y")))