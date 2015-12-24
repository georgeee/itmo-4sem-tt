{-# LANGUAGE PackageImports, FlexibleContexts #-}
module ExtendedLambda.Normalization (NormMonad, repeatNorm, runNormMonad, runNormMonad'
                                    , testNormMonad, testNormalize, normalize) where

import ExtendedLambda.Types
import ExtendedLambda.Base

import Common
import Debug.Trace
import Data.List
import Data.Foldable as F
import Control.Monad.Except
import Control.Monad.Trans.Either
import Control.Monad.Error.Class
import Control.Monad.State.Strict
import Control.Applicative
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS
import qualified Data.LinkedHashMap.IntMap as LHM

traceM' x y = y
--traceM' x y = y >>= \y' -> trace (x ++ " ==> " ++ (show y')) (return y')

trace' x y = y

mkApp2 :: ExtendedLambdaBase ExtendedLambda -> ExtendedLambda -> ExtendedLambda
mkApp2 e = noContext . (noContext e :@)

mkApp3 :: ExtendedLambdaBase ExtendedLambda -> ExtendedLambdaBase ExtendedLambda -> ExtendedLambda -> ExtendedLambda
mkApp3 e1 e2 = noContext . ((:@) . noContext $ noContext e1 :@ noContext e2)

testNormalize = testNormMonad normalize

normalize :: ExtendedLambda -> NormMonad Int ExtendedLambda
normalize = impl HM.empty
  where --impl :: HM.HashMap Var ExtendedLambda -> ExtendedLambda -> NormMonad Int ExtendedLambda
        impl = repeatNorm . impl''
        impl'' m (ls ::= e) = (impl' m' e >>= lift . mergeContexts' ls) `catchError` (lift . mergeContexts' ls >=> left)
          where m' = foldr' (uncurry HM.insert) m $ LHM.toList ls
        --impl' :: HM.HashMap Var ExtendedLambda -> ExtendedLambdaBase ExtendedLambda -> NormMonad Int ExtendedLambda
        impl' m ((_ ::= If) :@ (_ ::= B b)) = trace' "if1 " $ return $ if b then elIfTrue else elIfFalse
        impl' m ((_ ::= If) :@ p) = trace' "if2 " $ mkApp2 If <?$> impl m p
        impl' m ((_ ::= (_ ::= IOp op) :@ (_ ::= I i)) :@ (_ ::= I j)) = trace' "iop1 " $ return . noContext . I $ iop op i j
        impl' m ((_ ::= (_ ::= IOp op) :@ (_ ::= I i)) :@ p) = trace' "iop2 " $ mkApp3 (IOp op) (I i) <?$> impl m p
        impl' m ((_ ::= IOp op) :@ p) = trace' "iop3 " $ mkApp2 (IOp op) <?$> impl m p
        impl' m ((_ ::= (_ ::= OrdOp op) :@ (_ ::= I i)) :@ (_ ::= I j)) = trace' "ordOp1 " $ return . noContext . B $ ordOp op i j
        impl' m ((_ ::= (_ ::= OrdOp op) :@ (_ ::= I i)) :@ p) = trace' "ordOp2 " $ mkApp3 (OrdOp op) (I i) <?$> impl m p
        impl' m ((_ ::= OrdOp op) :@ p) = trace' "ordOp3 " $ mkApp2 (OrdOp op) <?$> impl m p
        impl' m ((_ ::= Y) :@ f) = trace' "Y " $ return $ noContext (f :@ noContext (noContext Y :@ f))
        impl' m ((_ ::= PrL) :@ (ctx ::= a :~ b)) = trace' "PrL1 " $ lift (mergeContexts' ctx a)
        impl' m ((_ ::= PrR) :@ (ctx ::= a :~ b)) = trace' "PrR1 " $ lift (mergeContexts' ctx b)
        impl' m ((_ ::= PrL) :@ p) = trace' "PrL2 " $ mkApp2 PrL <?$> impl m p
        impl' m ((_ ::= PrR) :@ p) = trace' "PrR2 " $ mkApp2 PrR <?$> impl m p
        impl' m ((_ ::= Case) :@ (xCtx ::= (_ ::= InL) :@ x)) = trace' "CaseL " $ do
                  x' <- lift (mergeContexts' xCtx x)
                  return $ noContext $ elCaseL :@ x'
        impl' m ((_ ::= Case) :@ (yCtx ::= (_ ::= InR) :@ y)) = trace' "CaseR " $ do
                  y' <- lift (mergeContexts' yCtx y)
                  return $ noContext $ elCaseR :@ y'
        impl' m ((_ ::= Case) :@ p) = trace' "Case3 " $ mkApp2 Case <?$> impl m p
        impl' m ((ctx ::= Abs v s) :@ e) = traceM' ("Abs " ++ (show (v, s, e))) $ lift (mergeContexts ctx (LHM.singleton v e) >>= flip mergeContexts' s)
        impl' m (l :@ r) = trace' "App1 " $ (noContext . (:@ r) <?$> impl m l)
        impl' m (V v) = trace' ("Var " ++ (show $ (v, v `HM.lookup` m))) $ case v `HM.lookup` m of
                          Just e -> return e
                          _ -> left $ noContext (V v)
        impl' _ e = trace' ("Other: " ++ (show e)) $ left $ noContext e




