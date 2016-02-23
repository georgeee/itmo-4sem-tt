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
  where impl m _thRef = do
              traceM' $ return $ "Digged to thRef " ++ show _thRef ++ ", within context: " ++ (show m)
              thRef <- joinCtx m =<< getRedirect _thRef
              if thRef /= _thRef
                 then traceM' $ return $ "Merged contexts, new thRef: " ++ show thRef
                 else return ()
              th <- getThunk thRef
              if thNormalized th
                 then left thRef
                 else encloseCtx thRef
                        >> ( (repeatNorm impl' thRef >>= \thRef' -> handleRes thRef thRef' >> return thRef')
                                `catchError` \thRef' -> handleRes thRef thRef' >> left thRef')
        handleRes thRef thRef' = do
          updThunk thRef' (\s -> s { thNormalized = True })
          if thRef /= thRef'
             then setRedirect thRef thRef'
             else return ()


        impl' :: ThunkRef -> NormMonad ThunkState ThunkRef
        impl' thRef = do
              traceM' $ thShowIdent 0 thRef >>= return . (++) "Traversing to expr = "
              th <- getThunk thRef
              let ctx = thContext th
              case thExpr th of
                  V v -> let substVar varRef = do
                                traceM' $ return . (("Substituting to var " ++ v ++ ": ") ++) =<< thShowIdent 0 varRef
                                varRef' <- obtain varRef >>= joinCtx ctx
                                release thRef
                                return varRef'
                          in case v `HM.lookup` ctx of
                               Just varRef -> substVar varRef
                               _ -> left thRef
                  pTh :@ qTh -> do p <- getThunkExpr pTh
                                   q <- getThunkExpr qTh
                                   pCtx <- thContext <$> getThunk pTh
                                   qCtx <- thContext <$> getThunk qTh
                                   let digLeft = trace' "digLeft" $ dig alterLeft pTh
                                       digRight = trace' "digRight" $ dig alterRight qTh
                                       alterLeft pTh' = updThunk thRef (\s -> s { thExpr = pTh' :@ qTh }) >> return thRef
                                       alterRight qTh' = updThunk thRef (\s -> s { thExpr = pTh :@ qTh' }) >> return thRef
                                       dig alter comp = (impl ctx comp >>= alter)
                                            `catchError` \comp' -> if comp == comp'
                                                                      then left thRef
                                                                      else alter comp' >>= left
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
                                                     qTh' <- joinCtx ctx qTh
                                                     traceM' $ return . ("qTh' " ++) =<< thShowIdent 0 qTh'
                                                     joinCtx ctx =<< joinCtx (HM.singleton v qTh') =<< joinCtx pCtx s
                                     Y -> do restTh <- newThunk th { thContext = HM.empty }
                                             obtain qTh
                                             updThunk thRef (\s -> s { thExpr = qTh :@ restTh })
                                             return thRef
                                     Case -> case q of
                                              qlTh :@ qrTh -> do ql <- getThunkExpr qlTh
                                                                 case ql of
                                                                   InL -> do release pTh
                                                                             release qTh
                                                                             release qlTh
                                                                             cL <- obtain =<< gets caseL
                                                                             updThunk thRef (\s -> s { thExpr = cL :@ qrTh })
                                                                             return thRef
                                                                   InR -> do release pTh
                                                                             release qTh
                                                                             release qlTh
                                                                             cR <- obtain =<< gets caseR
                                                                             updThunk thRef (\s -> s { thExpr = cR :@ qrTh })
                                                                             return thRef
                                                                   _ -> digRight
                                              _ -> digRight
                                     plTh :@ prTh -> do pl <- getThunkExpr plTh
                                                        pr <- getThunkExpr prTh
                                                        case (pl, pr, q) of
                                                         (IOp op, I i, I j) -> do
                                                           release pTh
                                                           release qTh
                                                           release plTh
                                                           release prTh
                                                           updThunk thRef (\s -> s { thExpr = I (iop op i j)
                                                                                   , thContext = HM.empty })
                                                           return thRef
                                                         (IOp _, I _, _) -> digRight
                                                         (OrdOp op, I i, I j) -> do
                                                           release pTh
                                                           release qTh
                                                           release plTh
                                                           release prTh
                                                           updThunk thRef (\s -> s { thExpr = B (ordOp op i j)
                                                                                   , thContext = HM.empty })
                                                           return thRef
                                                         (OrdOp _, I _, _) -> digRight
                                                         _ -> digLeft
                                     _ -> digLeft
                  _ -> left thRef
