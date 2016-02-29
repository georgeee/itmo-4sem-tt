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
import Control.Monad.Error.Class (catchError, MonadError, throwError)
import Control.Monad.Trans.Either
import qualified "unordered-containers" Data.HashMap.Strict as HM
import ExtendedLambda.Types
import ExtendedLambda.Base
import Control.Monad.State.Strict

testThunkNormalize s run = runNormMonadSt run chain
 --                          in case res of
 --                            Left s -> Left s
 --                            Right (Left e, thState) -> Right . Left $ run (thShowIdent 0 e) thState
 --                            Right (Right e, thState) -> Right . Right $ run (thShowIdent 0 e) thState
  where chain = testElParseSt s >>= normalizeRecursion >>= convertToThunks >>= normalize
        chainP = (chain >>= thShowIdent 0) `catchError` (thShowIdent >=> left)

normalize :: (MonadThunkState ref m, MonadError String m) => ref -> EitherT ref m ref
normalize = \r -> do
    iT <- convertToThunks elIfTrue
    iF <- convertToThunks elIfFalse
    cL <- convertToThunks elCaseL
    cR <- convertToThunks elCaseR
    bImpl iT iF cL cR r
  where bImpl :: (MonadThunkState ref m, MonadError String m) => ref -> ref -> ref -> ref -> ref -> EitherT ref m ref
        bImpl ifTrueTh ifFalseTh caseL caseR = impl HM.empty
          where
           impl m _thRef = do
               traceM' $ return $ "Digged to thRef " ++ show _thRef ++ ", within context: " ++ (show m)
               _thRef' <- trace' "@@ 0" . joinCtx m =<< getCached _thRef
               if _thRef' /= _thRef
                  then traceM' $ return $ "Merged contexts, new thRef: " ++ show _thRef'
                  else return ()
               repeatNorm (withCache impl') _thRef'
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
