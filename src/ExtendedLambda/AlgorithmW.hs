{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, PackageImports, FlexibleContexts #-}
module ExtendedLambda.AlgorithmW where

import ExtendedLambda.Types
import ExtendedLambda.Base
import Unification
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS
import Control.Monad
import Data.Foldable
import Control.Monad.State.Strict

typeBool = Const "Bool"
typeInt = Const "Int"
typeAnd = Function "&"
typeOr = Function "|"

type TVSet = HS.HashSet Name
type Subst = HM.HashMap Name ELType

infixr 2 :>:
infixr 3 :|:
infixr 4 :&:
infixl 1 :::
data ELType = TV Name | TBool | TInt
            | ELType :>: ELType
            | ELType :|: ELType
            | ELType :&: ELType

data ELTypeScheme = TVSet ::: ELType

class ELTypeHolder t where
  ftv :: t -> TVSet
  subst :: Subst -> t -> t


instance ELTypeHolder ELType where
  ftv t = execState (impl t) HS.empty
    where impl (TV v) = modify (HS.insert v)
          impl (l :>: r) = impl l >> impl r
          impl (l :|: r) = impl l >> impl r
          impl (l :&: r) = impl l >> impl r
          impl _ = return ()
  subst s (TV v) = case v `HM.lookup` s of
                     Just t -> t
                     _ -> TV v
  subst s (l :>: r) = subst s l :>: subst s r
  subst s (l :&: r) = subst s l :&: subst s r
  subst s (l :|: r) = subst s l :|: subst s r
  subst s e = e

instance ELTypeHolder ELTypeScheme where
  ftv (vs ::: t) = ftv t `HS.difference` vs
  subst s (vs ::: t) = vs ::: subst (foldr HM.delete s vs) t

instance ELTypeHolder a => ELTypeHolder [a] where
  ftv = foldr ((HS.union) . ftv) HS.empty
  subst = map . subst

instance ELTypeHolder Subst where
  ftv m = ftv $ HM.elems m
  subst s m = HM.map (subst (foldr HM.delete s $ HM.keys m)) m

generalize :: Subst -> ELType -> ELTypeScheme
generalize s t = ftv t `HS.difference` ftv s ::: t

instantiate :: MonadState Int m => ELTypeScheme -> m ELType
instantiate (ctx ::: e) = flip subst e <$> foldM (\m v -> freshId v >>= \nv -> return $ HM.insert v (TV nv) m) HM.empty ctx

initTypeEnv = HM.empty

algorithmW :: MonadState Int m => ExtendedLambda -> m (Either String (Subst, ELTypeScheme))
algorithmW e = w initTypeEnv e
  where w s (ctx ::= e) = undefined

