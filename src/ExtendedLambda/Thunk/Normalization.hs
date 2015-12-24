{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module ExtendedLambda.Thunk.Normalization where

import ExtendedLambda.Thunk.Base
import Control.Monad.State.Class
import Data.Foldable
import Common
import Control.Monad.Error.Class
import Control.Monad.Trans.Either
import qualified "unordered-containers" Data.HashMap.Strict as HM
import ExtendedLambda.Types
import ExtendedLambda.Base
import Control.Monad.State.Strict

normalize :: ThunkRef -> NormMonad ThunkState ThunkRef
normalize = impl HM.empty
  where impl = repeatNorm . impl'
        impl' m thRef =
           do th <- getThunk thRef
              let m' = foldr' (uncurry HM.insert) m $ HM.toList ctx
                  ctx = thContext th
              case thExpr th of
                  V v -> case v `HM.lookup` m' of
                           Just th -> obtain th
                           _ -> left thRef
                  pTh :@ qTh -> do p <- getThunkExpr pTh
                                   q <- getThunkExpr qTh
                                   pCtx <- thContext <$> getThunk pTh
                                   qCtx <- thContext <$> getThunk qTh
                                   case p of
                                     IOp _ -> (do qTh' <- impl m' qTh
                                                  updThunk thRef $ \th -> th { thExpr = pTh :@ qTh' }
                                                  return thRef) `catchError` const (left thRef)
                                     OrdOp _ -> (do qTh' <- impl m' qTh
                                                    updThunk thRef $ \th -> th { thExpr = pTh :@ qTh' }
                                                    return thRef) `catchError` const (left thRef)
                                     If -> case q of
                                             (B b) -> do release pTh
                                                         release qTh
                                                         release thRef
                                                         obtain =<< if b
                                                                       then gets ifTrueTh
                                                                       else gets ifFalseTh
                                             _ -> (do qTh' <- impl m' qTh
                                                      updThunk thRef $ \th -> th { thExpr = pTh :@ qTh' }
                                                      return thRef) `catchError` const (left thRef)
                                     PrL -> case q of
                                              aTh :~ bTh -> do
                                                release pTh
                                                release qTh
                                                release bTh
                                                release thRef
                                                joinCtx ctx =<< joinCtx qCtx aTh
                                              _ -> (do qTh' <- impl m' qTh
                                                       updThunk thRef $ \th -> th { thExpr = pTh :@ qTh' }
                                                       return thRef) `catchError` const (left thRef)
                                     PrR -> case q of
                                              aTh :~ bTh -> do
                                                release pTh
                                                release qTh
                                                release aTh
                                                release thRef
                                                joinCtx ctx =<< joinCtx qCtx bTh
                                              _ -> (do qTh' <- impl m' qTh
                                                       updThunk thRef $ \th -> th { thExpr = pTh :@ qTh' }
                                                       return thRef) `catchError` const (left thRef)
                                     (Abs v s) -> do release pTh
                                                     release thRef
                                                     joinCtx ctx =<< joinCtx (HM.singleton v qTh) =<< joinCtx pCtx s
                                     Y -> do restTh <- newThunk th { thContext = HM.empty }
                                             obtain qTh
                                             updThunk thRef $ \th -> th { thExpr = qTh :@ restTh }
                                             return thRef
                                     Case -> case q of
                                              qlTh :@ qrTh -> do ql <- getThunkExpr qlTh
                                                                 case ql of
                                                                   InL -> do release pTh
                                                                             release qTh
                                                                             release qlTh
                                                                             cL <- obtain =<< gets caseL
                                                                             updThunk thRef $ \th -> th { thExpr = cL :@ qrTh }
                                                                             return thRef
                                                                   InR -> do release pTh
                                                                             release qTh
                                                                             release qlTh
                                                                             cR <- obtain =<< gets caseR
                                                                             updThunk thRef $ \th -> th { thExpr = cR :@ qrTh }
                                                                             return thRef
                                                                   _ -> (do qTh' <- impl m' qTh
                                                                            updThunk thRef $ \th -> th { thExpr = pTh :@ qTh' }
                                                                            return thRef) `catchError` const (left thRef)
                                              _ -> (do qTh' <- impl m' qTh
                                                       updThunk thRef $ \th -> th { thExpr = pTh :@ qTh' }
                                                       return thRef) `catchError` const (left thRef)
                                     plTh :@ prTh -> do pl <- getThunkExpr plTh
                                                        pr <- getThunkExpr prTh
                                                        case (pl, pr, q) of
                                                         (IOp op, I i, I j) -> do release pTh
                                                                                  release qTh
                                                                                  release plTh
                                                                                  release prTh
                                                                                  updThunk thRef $ \th -> th { thExpr = I (iop op i j) }
                                                                                  return thRef
                                                         (IOp _, I _, _) -> (do qTh' <- impl m' qTh
                                                                                updThunk thRef $ \th -> th { thExpr = pTh :@ qTh' }
                                                                                return thRef) `catchError` const (left thRef)
                                                         (OrdOp op, I i, I j) -> do release pTh
                                                                                    release qTh
                                                                                    release plTh
                                                                                    release prTh
                                                                                    updThunk thRef $ \th -> th { thExpr = B (ordOp op i j) }
                                                                                    return thRef
                                                         (OrdOp _, I _, _) -> (do qTh' <- impl m' qTh
                                                                                  updThunk thRef $ \th -> th { thExpr = pTh :@ qTh' }
                                                                                  return thRef) `catchError` const (left thRef)
                                                         _ -> (do pTh' <- impl m' pTh
                                                                  updThunk thRef $ \th -> th { thExpr = pTh' :@ qTh }
                                                                  return thRef) `catchError` const (left thRef)
                                     _ -> (do pTh' <- impl m' pTh
                                              updThunk thRef $ \th -> th { thExpr = pTh' :@ qTh }
                                              return thRef) `catchError` const (left thRef)
                  _ -> left thRef
