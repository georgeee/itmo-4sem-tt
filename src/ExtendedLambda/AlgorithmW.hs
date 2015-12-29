{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, PackageImports, FlexibleContexts #-}
module ExtendedLambda.AlgorithmW where

import Debug.Trace
import ExtendedLambda.Types
import ExtendedLambda.Base
import Unification
import Common
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS
import qualified Data.LinkedHashMap.IntMap as LHM
import Control.Monad
import Control.Monad.Trans.Either
import Data.Foldable
import Data.List
import Control.Monad.State.Strict

type TVSet = HS.HashSet Name
type Subst = HM.HashMap Name ELType
type TypeEnv = HM.HashMap Var ELTypeScheme

infixr 2 :>:
infixr 3 :|:
infixr 4 :&:
infixl 1 :::
data ELType = TV Name | TBool | TInt
            | ELType :>: ELType
            | ELType :|: ELType
            | ELType :&: ELType

instance Show ELType where
  show (TV x) = x
  show (l@(_ :>: _) :>: r) = "(" ++ show l ++ ") -> " ++ show r
  show (l :>: r) = show l ++ " -> " ++ show r
  show (l :|: r) = "(" ++ show l ++ ") | (" ++ show r ++ ")"
  show (l :&: r) = "(" ++ show l ++ ") & (" ++ show r ++ ")"
  show TBool = "Bool"
  show TInt = "Int"

data ELTypeScheme = TVSet ::: ELType

instance Show ELTypeScheme where
  show (vs ::: t) = (if HS.null vs then "" else "∀ " ++ intercalate " " (map show $ HS.toList vs) ++ ". ") ++ show t

emptyScheme = (HS.empty :::)

infixl 5 >*

class ELTypeHolder t where
  ftv :: t -> TVSet
  (>*) :: Subst -> t -> t


instance ELTypeHolder ELType where
  ftv t = execState (impl t) HS.empty
    where impl (TV v) = modify (HS.insert v)
          impl (l :>: r) = impl l >> impl r
          impl (l :|: r) = impl l >> impl r
          impl (l :&: r) = impl l >> impl r
          impl _ = return ()
  s >* (TV v) = case v `HM.lookup` s of
                     Just t -> t
                     _ -> TV v
  s >* (l :>: r) = s >* l :>: s >* r
  s >* (l :&: r) = s >* l :&: s >* r
  s >* (l :|: r) = s >* l :|: s >* r
  s >* e = e

instance ELTypeHolder ELTypeScheme where
  ftv (vs ::: t) = ftv t `HS.difference` vs
  s >* (vs ::: t) = vs ::: foldr HM.delete s vs >* t

instance ELTypeHolder a => ELTypeHolder [a] where
  ftv = foldr ((HS.union) . ftv) HS.empty
  (>*) = map . (>*)

instance ELTypeHolder TypeEnv where
  ftv m = ftv $ HM.elems m
  s >* m = HM.map (s >*) m

instance ELTypeHolder ELTyped where
  s >* (ELTyped ctx e t) = ELTyped (LHM.map (s >*) ctx) (s >* e) (s >* t)
  ftv = undefined

instance ELTypeHolder (ExtendedLambdaBase ELTyped) where
  s >* (Abs v e) = Abs v (s >* e)
  s >* (l :~ r) = (s >* l) :~ (s >* r)
  s >* (l :@ r) = (s >* l) :@ (s >* r)
  s >* e = e
  ftv = undefined

infixl 6 >**
(>**) :: Subst -> Subst -> Subst
s1 >** s2 = (HM.map (s1 >*) s2) `HM.union` s1


generalize :: TypeEnv -> ELType -> ELTypeScheme
generalize s t = ftv t `HS.difference` ftv s ::: t

instantiate :: MonadState Int m => ELTypeScheme -> m ELType
instantiate (ctx ::: e) = (>* e) <$> foldM (\m v -> freshId >>= \nv -> return $ HM.insert v (TV nv) m) HM.empty ctx

findType :: MonadState Int m => ExtendedLambda -> EitherT String m (ELType, ELTyped)
findType e = do (subst, t, elt) <- w HM.empty e
                return (subst >* t, subst >* elt)



data ELTyped = ELTyped { eltCtx :: LHM.LinkedHashMap Var ELTyped, eltExpr :: ExtendedLambdaBase ELTyped, eltType :: ELType }
instance ELambdaContainer ELTyped where
  extractEl = eltExpr
instance IdentShow ELTyped where
  showIdent i (ELTyped ctx e t) = if LHM.null ctx then showET i e t else let i' = i + 1 in
              concat [ "\n" ++ (sps $ i * 2) ++ "(let " ++ (intercalate (",\n" ++ (sps $ i * 2 + 4)) $ showLBs i' ctx)
                     , "\n" ++ (sps $ i' * 2 - 1) ++ "in " ++ (showIdent i' e ++ " :: " ++ show t) ++ ")"
                     ]
    where showLBs i = map (\(v, s) -> v ++ " = " ++ showET' i s) . LHM.toList
          showET :: Int -> ExtendedLambdaBase ELTyped -> ELType -> String
          showET i e@(V _) t = "[ " ++ showIdent i e ++ " :: " ++ show t ++ " ]"
          showET i e t = showIdent i e
          showET' :: Int -> ELTyped -> String
          showET' i e@(ELTyped ctx e' t) = showIdent i e ++ " :: " ++ show t
p i s = (replicate (i*2) ' ') ++ s
sps = flip replicate ' '
instance Show ELTyped where
  show = showIdent 0

w :: MonadState Int m => TypeEnv -> ExtendedLambda -> EitherT String m (Subst, ELType, ELTyped)
w s (m ::= e2) = w'' LHM.empty s m
  where w'' elts s m = if LHM.null m
                          then do (subst, t, e) <- w' s e2
                                  return (subst, t, ELTyped elts e t)
                          else let x = head $ LHM.keys m
                                   e1 = m LHM.! x
                                   m' = x `LHM.delete` m
                                in do (s1, t1, elt) <- w s e1
                                      let s1s = s1 >* s
                                          s' = HM.insert x (generalize s1s t1) s1s
                                      (s2, t2, elt) <- w'' (LHM.insert x elt elts)  s' m'
                                      return (s2 >** s1, t2, elt)

w' :: MonadState Int m => TypeEnv -> ExtendedLambdaBase ExtendedLambda -> EitherT String m (Subst, ELType, ExtendedLambdaBase ELTyped)
w' s (V x) = case x `HM.lookup` s of
               Just t -> (,,) HM.empty <$> instantiate t <*> pure (V x)
               _ -> left $ "Variable " ++ x ++ " not found"
w' s (Abs x e) = do b <- TV <$> freshId
                    (s1, t1, e') <- w (HM.insert x (emptyScheme b) s) e
                    return (s1, s1 >* b :>: t1, Abs x e')
w' s (e1 :~ e2) = do (s1, t1, e1') <- w s e1
                     (s2, t2, e2') <- w (s1 >* s) e2
                     return (s2 >** s1, s2 >* t1 :&: t2, e1' :~ e2')
w' s (e1 :@ e2) = do (s1, t1, e1') <- w s e1
                     (s2, t2, e2') <- w (s1 >* s) e2
                     b <- TV <$> freshId
                     s3 <- mgu (s2 >* t1) (t2 :>: b)
                     return (s3 >** s2 >** s1, s3 >* b, e1' :@ e2')
w' s (I i) = return (HM.empty, TInt, I i)
w' s (B b) = return (HM.empty, TBool, B b)
w' s Y = (,,) HM.empty <$> instBase ((a :>: a) :>: a) <*> pure Y
w' s PrL = (,,) HM.empty <$> instBase (a :&: b :>: a) <*> pure PrL
w' s PrR = (,,) HM.empty <$> instBase (a :&: b :>: b) <*> pure PrR
w' s InL = (,,) HM.empty <$> instBase (a :>: a :|: b) <*> pure InL
w' s InR = (,,) HM.empty <$> instBase (b :>: a :|: b) <*> pure InR
w' s Case = (,,) HM.empty <$> instBase (a :|: b :>: (a :>: c) :>: (b :>: c) :>: c) <*> pure Case
w' s If = (,,) HM.empty <$> instBase (TBool :>: a :>: a :>: a) <*> pure If
w' s (IOp op) = return (HM.empty, TInt :>: TInt :>: TInt, IOp op)
w' s (OrdOp op) = return (HM.empty, TInt :>: TInt :>: TBool, OrdOp op)
--w' s e = error $ "fuck: " ++ show s ++ " " ++ show e

a = TV "a"
b = TV "b"
c = TV "c"

instBase :: MonadState Int m => ELType -> m ELType
instBase = instantiate . generalize HM.empty

mgu :: MonadState Int m => ELType -> ELType -> EitherT String m Subst
mgu t1 t2 = let t1' = typeToTerm t1
                t2' = typeToTerm t2
             in either (left . show) (right . solvedToSubst) $ unify [t1' := t2']
             --in trace ("fuck2 " ++ show [t1' := t2']) $ return HM.empty

solvedToSubst :: SolvedSystem -> Subst
solvedToSubst = HM.map termToType

termToType :: Term -> ELType
termToType (Var v) = TV v
termToType (Const "Bool") = TBool
termToType (Const "Int") = TInt
termToType (Function "->" (t1:t2:[])) = termToType t1 :>: termToType t2
termToType (Function "&" (t1:t2:[])) = termToType t1 :&: termToType t2
termToType (Function "|" (t1:t2:[])) = termToType t1 :|: termToType t2

typeBool = Const "Bool"
typeInt = Const "Int"

typeToTerm :: ELType -> Term
typeToTerm (TV v) = Var v
typeToTerm TBool = Const "Bool"
typeToTerm TInt = Const "Int"
typeToTerm (t1 :>: t2) = Function "->" [typeToTerm t1, typeToTerm t2]
typeToTerm (t1 :&: t2) = Function "&" [typeToTerm t1, typeToTerm t2]
typeToTerm (t1 :|: t2) = Function "|" [typeToTerm t1, typeToTerm t2]

