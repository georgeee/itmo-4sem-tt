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

infixl :* 5
class ELTypeHolder t where
  ftv :: t -> TVSet
  (:*) :: Subst -> t -> t


instance ELTypeHolder ELType where
  ftv t = execState (impl t) HS.empty
    where impl (TV v) = modify (HS.insert v)
          impl (l :>: r) = impl l >> impl r
          impl (l :|: r) = impl l >> impl r
          impl (l :&: r) = impl l >> impl r
          impl _ = return ()
  s :* (TV v) = case v `HM.lookup` s of
                     Just t -> t
                     _ -> TV v
  s :* (l :>: r) = s :* l :>: s :* r
  s :* (l :&: r) = s :* l :&: s :* r
  s :* (l :|: r) = s :* l :|: s :* r
  s :* e = e

instance ELTypeHolder ELTypeScheme where
  ftv (vs ::: t) = ftv t `HS.difference` vs
  s :* (vs ::: t) = vs ::: foldr HM.delete s vs :* t

instance ELTypeHolder a => ELTypeHolder [a] where
  ftv = foldr ((HS.union) . ftv) HS.empty
  (:*) = map . (:*)

instance ELTypeHolder Subst where
  ftv m = ftv $ HM.elems m
  s :* m = HM.map ((:*) (foldr HM.delete s $ HM.keys m)) m

generalize :: Subst -> ELType -> ELTypeScheme
generalize s t = ftv t `HS.difference` ftv s ::: t

instantiate :: MonadState Int m => ELTypeScheme -> m ELType
instantiate (ctx ::: e) = (:* e) <$> foldM (\m v -> freshId v >>= \nv -> return $ HM.insert v (TV nv) m) HM.empty ctx

initTypeEnv = HM.empty

algorithmW :: MonadState Int m => ExtendedLambda -> EitherT String m (Subst, ELTypeScheme)
algorithmW e = w initTypeEnv e
  where w s (m ::= e2) = if LHM.null m
                            then w' s m
                            else let k = head $ LHM.keys m
                                     e1 = m LHM.! k
                                     m' = k `LHM.delete` m
                                  in do (s1, t1) <- w s a
                                        let s1s = s1 :* s
                                            s' = HM.insert x (generalize s1s t1) s1s
                                        (s2, t2) <- w s' (as ::= e)
                                        return (s2 :* s1, t2)


