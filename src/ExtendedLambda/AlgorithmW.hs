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
  deriving Show

data ELTypeScheme = TVSet ::: ELType
  deriving Show

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

infixl 6 >**
(>**) :: Subst -> Subst -> Subst
s1 >** s2 = (HM.map (s1 >*) s2) `HM.union` s1


generalize :: TypeEnv -> ELType -> ELTypeScheme
generalize s t = ftv t `HS.difference` ftv s ::: t

instantiate :: MonadState Int m => ELTypeScheme -> m ELType
instantiate (ctx ::: e) = (>* e) <$> foldM (\m v -> freshId >>= \nv -> return $ HM.insert v (TV nv) m) HM.empty ctx

findType :: MonadState Int m => ExtendedLambda -> EitherT String m (Subst, ELType)
findType e = w HM.empty e

yType = HS.singleton "a" ::: (TV "a" :>: TV "a") :>: TV "a"

w :: MonadState Int m => TypeEnv -> ExtendedLambda -> EitherT String m (Subst, ELType)
w s (m ::= e2) = if LHM.null m
                    then w' s e2
                    else let x = head $ LHM.keys m
                             e1 = m LHM.! x
                             m' = x `LHM.delete` m
                          in do (s1, t1) <- w s e1
                                let s1s = s1 >* s
                                    s' = HM.insert x (generalize s1s t1) s1s
                                (s2, t2) <- w s' (m' ::= e2)
                                return (s2 >** s1, t2)

w' :: MonadState Int m => TypeEnv -> ExtendedLambdaBase ExtendedLambda -> EitherT String m (Subst, ELType)
w' s (V x) = case x `HM.lookup` s of
               Just t -> (,) HM.empty <$> instantiate t
               _ -> left $ "Variable " ++ x ++ " not found"
w' s (Abs x e) = do b <- TV <$> freshId
                    (s1, t1) <- w (HM.insert x (emptyScheme b) s) e
                    return (s1, s1 >* b :>: t1)
--w' s (e1 :~ e2) = do (s1, t1) <- w s e1
--                     (s2, t2) <- w s e2
--                     return (s, s1 *> t1 :&: t2)
w' s (e1 :@ e2) = do (s1, t1) <- w s e1
                     (s2, t2) <- w (s1 >* s) e2
                     b <- TV <$> freshId
                     s3 <- mgu (s2 >* t1) (t2 :>: b)
                     return (s3 >** s2 >** s1, s3 >* b)
w' s (I _) = return (HM.empty, TInt)
w' s (B _) = return (HM.empty, TBool)
w' s Y = (,) HM.empty <$> instBase ((a :>: a) :>: a)
w' s PrL = (,) HM.empty <$> instBase (a :&: b :>: a)
w' s PrR = (,) HM.empty <$> instBase (a :&: b :>: b)
w' s InL = (,) HM.empty <$> instBase (a :>: a :|: b)
w' s InR = (,) HM.empty <$> instBase (b :>: a :|: b)
w' s Case = (,) HM.empty <$> instBase (a :|: b :>: (a :>: c) :>: (b :>: c) :>: c)
w' s If = (,) HM.empty <$> instBase (TBool :>: a :>: a :>: a)
w' s (IOp _) = return (HM.empty, TInt :>: TInt :>: TInt)
w' s (OrdOp _) = return (HM.empty, TInt :>: TInt :>: TBool)
w' s e = error $ "fuck: " ++ show s ++ " " ++ show e

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

