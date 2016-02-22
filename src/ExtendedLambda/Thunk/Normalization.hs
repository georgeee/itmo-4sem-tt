{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module ExtendedLambda.Thunk.Normalization where

import Debug.Trace
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

testThunkNormalize s = let res = runNormMonadSt chain
                        in case res of
                             Left s -> Left s
                             Right (Left e, thState) -> Right . Left $ evalState (printE e) thState
                             Right (Right e, thState) -> Right . Right $ evalState (printE e) thState
  where chain = testElParseSt s >>= normalizeRecursion >>= convertToThunks >>= normalize
        printE e = do e' <- thShowIdent 0 e
                      sz <- gets (HM.size . thunks)
                      cnt <- gets (idCounter)
                      return $ e' ++ "  sz=" ++ show sz ++ "  cnt=" ++ show cnt

normalize :: ThunkRef -> NormMonad ThunkState ThunkRef
normalize = impl HM.empty
  where impl = repeatNorm . impl'
        impl' :: ThunkContext -> ThunkRef -> NormMonad ThunkState ThunkRef
        impl' m thRef =
           do s' <- thShowIdent 0 thRef
              traceM $ "Traversing to s'=" ++ s' ++ "\n m = " ++ (show m)
              th <- getThunk thRef
              let ctx = thContext th
              case thExpr th of
                  V v -> let substVar varRef = do release thRef
                                                  traceM . (("Substituting to var " ++ v) ++) =<< thShowIdent 0 varRef
                                                  obtain varRef
                          in case v `HM.lookup` m of
                               Just varRef -> substVar varRef
                               _ -> case v `HM.lookup` ctx of
                                     Just varRef -> substVar varRef
                                     _ -> left thRef
                  pTh :@ qTh -> do p <- getThunkExpr pTh
                                   q <- getThunkExpr qTh
                                   pCtx <- thContext <$> getThunk pTh
                                   qCtx <- thContext <$> getThunk qTh
                                   let digLeft = trace "digLeft" $
                                                 (do pTh' <- flip impl pTh =<< joinCtxM m ctx
                                                     release thRef
                                                     newThunk th { thExpr = pTh' :@ qTh }) `catchError` const (left thRef)
                                       digRight = trace "digRight" $
                                                  (do qTh' <- flip impl qTh =<< joinCtxM m ctx
                                                      release thRef
                                                      newThunk th { thExpr = pTh :@ qTh' }) `catchError` const (left thRef)
                                   case p of
                                     IOp _ -> digRight
                                     OrdOp _ -> digRight
                                     If -> case q of
                                             (B b) -> do release pTh
                                                         release qTh
                                                         release thRef
                                                         obtain =<< if b
                                                                       then gets ifTrueTh
                                                                       else gets ifFalseTh
                                             _ -> digRight
                                     PrL -> case q of
                                              aTh :~ bTh -> do
                                                release pTh
                                                release qTh
                                                release bTh
                                                release thRef
                                                joinCtx ctx =<< joinCtx qCtx aTh
                                              _ -> digRight
                                     PrR -> case q of
                                              aTh :~ bTh -> do
                                                release pTh
                                                release qTh
                                                release aTh
                                                release thRef
                                                joinCtx ctx =<< joinCtx qCtx bTh
                                              _ -> digRight
                                     (Abs v s) -> do release pTh
                                                     release thRef
                                                     qTh' <- joinCtx m =<< joinCtx ctx qTh
                                                     traceM . ("qTh' " ++) =<< thShowIdent 0 qTh'
                                                     joinCtx ctx =<< joinCtx (HM.singleton v qTh') =<< joinCtx pCtx s
                                     Y -> do restTh <- newThunk th { thContext = HM.empty }
                                             obtain qTh
                                             release thRef
                                             newThunk th { thExpr = qTh :@ restTh }
                                     Case -> case q of
                                              qlTh :@ qrTh -> do ql <- getThunkExpr qlTh
                                                                 case ql of
                                                                   InL -> do release pTh
                                                                             release qTh
                                                                             release qlTh
                                                                             release thRef
                                                                             cL <- obtain =<< gets caseL
                                                                             newThunk th { thExpr = cL :@ qrTh }
                                                                   InR -> do release pTh
                                                                             release qTh
                                                                             release qlTh
                                                                             release thRef
                                                                             cR <- obtain =<< gets caseR
                                                                             newThunk th { thExpr = cR :@ qrTh }
                                                                   _ -> digRight
                                              _ -> digRight
                                     plTh :@ prTh -> do pl <- getThunkExpr plTh
                                                        pr <- getThunkExpr prTh
                                                        case (pl, pr, q) of
                                                         (IOp op, I i, I j) -> do release pTh
                                                                                  release qTh
                                                                                  release plTh
                                                                                  release prTh
                                                                                  release thRef
                                                                                  newThunk th { thExpr = I (iop op i j), thContext = HM.empty }
                                                         (IOp _, I _, _) -> digRight
                                                         (OrdOp op, I i, I j) -> do release pTh
                                                                                    release qTh
                                                                                    release plTh
                                                                                    release prTh
                                                                                    release thRef
                                                                                    newThunk th { thExpr = B (ordOp op i j), thContext = HM.empty }
                                                         (OrdOp _, I _, _) -> digRight
                                                         _ -> digLeft
                                     _ -> digLeft
                  _ -> left thRef
