{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module ExtendedLambda.Thunk.Normalization where

import Control.Monad.Trans.Reader (asks)
import Debug.Trace
import ExtendedLambda.Thunk.Base
import ExtendedLambda.Thunk.State
import Control.Monad.State.Class
import Data.Foldable
import Common
import Control.Monad.Error.Class (catchError)
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
normalize = \r -> createBasics >>= flip bImpl r
  where bImpl ThunkBasics { thIfFalse = ifFalseTh
                          , thIfTrue = ifTrueTh
                          , thCaseL = caseL
                          , thCaseR = caseR } = impl HM.empty
          where
           impl m _thRef = do
               traceM' $ return $ "Digged to thRef " ++ show _thRef ++ ", within context: " ++ (show m)
               _thRef' <- trace' "@@ 0" . joinCtx m =<< getCached _thRef
               if _thRef' /= _thRef
                  then traceM' $ return $ "Merged contexts, new thRef: " ++ show _thRef'
                  else return ()
               repeatNorm (withCache impl') _thRef'

           impl' :: ThunkRef -> NormMonad ThunkState ThunkRef
           impl' thRef = do
                 encloseCtx thRef
                 propagateCtx thRef
                 propagateCached thRef
                 traceM' $ thShowIdent 0 thRef >>= return . (++) "Traversing to expr = "
                 th <- getThunk thRef
                 let ctx = thContext th
                 case thExpr th of
                     V v -> let substVar varRef = do
                                   traceM' $ return . (("Substituting to var " ++ v ++ ": ") ++) =<< thShowIdent 0 varRef
                                   varRef' <- trace' "@@ 1" $ joinCtx ctx varRef
                                   return varRef'
                             in case v `HM.lookup` ctx of
                                  Just varRef -> substVar varRef
                                  _ -> left thRef
                     pTh :@ qTh -> do propagateCached pTh
                                      propagateCached qTh
                                      p <- thExpr <$> getThunk pTh
                                      q <- thExpr <$> getThunk qTh
                                      pCtx <- thContext <$> getThunk pTh
                                      qCtx <- thContext <$> getThunk qTh
                                      let digLeft = trace' "digLeft" $ dig alterLeft pTh
                                          digRight = trace' "digRight" $ dig alterRight qTh
                                          alterLeft pTh' = updThunk thRef (\s -> s { thExpr = pTh' :@ qTh }) >> return thRef
                                          alterRight qTh' = updThunk thRef (\s -> s { thExpr = pTh :@ qTh' }) >> return thRef
                                          dig alter comp = (impl ctx comp >>= alter)
                                               `catchError` \comp' -> if comp == comp'
                                                                         then left thRef
                                                                         else alter comp'
                                      case p of
                                        IOp _ -> digRight
                                        OrdOp _ -> digRight
                                        If -> case q of
                                                (B b) -> if b
                                                            then return ifTrueTh
                                                            else return ifFalseTh
                                                _ -> digRight
                                        PrL -> case q of
                                                 aTh :~ bTh -> do
                                                   trace' "@@ 2" . joinCtx ctx =<< trace' "@@ 3" (joinCtx qCtx aTh)
                                                 _ -> digRight
                                        PrR -> case q of
                                                 aTh :~ bTh -> do
                                                   trace' "@@ 4" . joinCtx ctx =<< trace' "@@ 5" (joinCtx qCtx bTh)
                                                 _ -> digRight
                                        (Abs v s) -> do
                                             qTh' <- trace' "@@ 6" $ joinCtx ctx qTh
                                             trace' "@@ 7" . joinCtx ctx =<< trace' "@@ 8" . joinCtx (HM.singleton v qTh') =<< trace' "@@ 9" ( joinCtx pCtx s)
                                        Y -> do restTh <- newThunk th { thContext = HM.empty }
                                                updThunk thRef (\s -> s { thExpr = qTh :@ restTh })
                                                return thRef
                                        Case -> case q of
                                                 qlTh :@ qrTh -> do propagateCached qlTh
                                                                    ql <- thExpr <$> getThunk qlTh
                                                                    case ql of
                                                                      InL -> do
                                                                         cL <- return caseL
                                                                         updThunk thRef (\s -> s { thExpr = cL :@ qrTh })
                                                                         return thRef
                                                                      InR -> do
                                                                         cR <- return caseR
                                                                         updThunk thRef (\s -> s { thExpr = cR :@ qrTh })
                                                                         return thRef
                                                                      _ -> digRight
                                                 _ -> digRight
                                        plTh :@ prTh -> do propagateCached plTh
                                                           propagateCached prTh
                                                           pl <- thExpr <$> getThunk plTh
                                                           pr <- thExpr <$> getThunk prTh
                                                           case (pl, pr, q) of
                                                            (IOp op, I i, I j) -> do
                                                              updThunk thRef (\s -> s { thExpr = I (iop op i j)
                                                                                      , thContext = HM.empty })
                                                              return thRef
                                                            (IOp _, I _, _) -> digRight
                                                            (OrdOp op, I i, I j) -> do
                                                              updThunk thRef (\s -> s { thExpr = B (ordOp op i j)
                                                                                      , thContext = HM.empty })
                                                              return thRef
                                                            (OrdOp _, I _, _) -> digRight
                                                            _ -> digLeft
                                        _ -> digLeft
                     _ -> left thRef
