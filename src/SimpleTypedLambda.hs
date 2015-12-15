{-# LANGUAGE PackageImports, FlexibleContexts #-}
module SimpleTypedLambda where

import Control.Monad.State
import qualified "unordered-containers" Data.HashMap.Strict as HM
import UntypedLambda
import Unification

renameAll :: UntypedLambda -> UntypedLambda
renameAll = flip evalState 0 . impl HM.empty
  where impl m (ULApp s r) = ULApp <$> impl m s <*> impl m r
        impl m (ULAbs x e) = inc >>= \i -> let m' = HM.insert x x' m
                                               x' = 'x' : (show i)
                                            in ULAbs x' <$> impl m' e
        impl m (ULVar x) = pure $ case x `HM.lookup` m of
                             Just n -> ULVar n
                             Nothing -> ULVar x
        inc = get <* modify (+1)

infixl 1 :>:
data SimpleType = (:>:) SimpleType SimpleType | V Name

instance Show SimpleType where
  show (V x) = x
  show (l :>: r@(_ :>: _)) = show l ++ " -> (" ++ (show r) ++ ")"
  show (l :>: r) = show l ++ " -> " ++  (show r)

toSimpleType :: Term -> SimpleType
toSimpleType (Var x) = V x
toSimpleType (Function "->" (x:y:[])) = toSimpleType x :>: toSimpleType y
toSimpleType e = error $ "No simple type for " ++ (show e)

findType :: UntypedLambda -> Either Equation (UntypedLambda, SimpleType, HM.HashMap Name SimpleType)
findType = impl . renameAll
  where impl e = let (t, eqs, vm) = convertForUnification e
                  in impl' t vm <$> unify eqs
          where impl' t vm m = (e, toSimpleType t, HM.mapWithKey (\k v -> maybe (V v) toSimpleType (k `HM.lookup` m)) vm)

infixl 2 ~>
(~>) l r = Function "->" [l, r]

convertForUnification :: UntypedLambda -> (Term, [Equation], HM.HashMap Name Name)
convertForUnification = f' . flip runState (0, HM.empty) . impl
  where f' ((t, eqs), (_, m)) = (t, eqs, m)
        impl :: UntypedLambda -> State (Int, HM.HashMap Name Name) (Term, [Equation])
        impl (ULVar x) = flip (,) [] . Var <$> tv x
        impl (ULApp p q) = impl' <$> tv' <*> impl p <*> impl q
          where impl' a (tp, ep) (tq, eq) = (Var a, (tp := tq ~> Var a) : ep ++ eq)
        impl (ULAbs x p) = impl' <$> tv x <*> impl p
          where impl' tx (tp, ep) = (Var tx ~> tp, ep)
        tv x = get >>= \(i, m) -> case x `HM.lookup` m of
                               Just t -> return t
                               Nothing -> let t = 't' : (show i)
                                           in put (i + 1, HM.insert x t m) >> return t
        tv' = get >>= \(i, m) -> put (i + 1, m) >> return ('t' : (show i))
