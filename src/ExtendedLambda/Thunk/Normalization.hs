{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances, BangPatterns,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module ExtendedLambda.Thunk.Normalization where

import Control.Monad.Trans.Reader (asks)
import Debug.Trace
import ExtendedLambda.Thunk.Base
import qualified ExtendedLambda.Thunk.State as ThSt
import qualified ExtendedLambda.Thunk.ST as ThST
import Control.Monad.State.Class
import Data.Foldable
import Common
import Control.Monad.Error.Class (catchError, MonadError, throwError)
import Control.Monad.Trans.Either hiding (left, right)
import Control.Monad.Trans.Except (Except, runExcept)
import qualified "unordered-containers" Data.HashMap.Strict as HM
import ExtendedLambda.Types
import ExtendedLambda.Base
import Control.Monad.State.Strict

evalStateT' :: Monad m => StateT ThSt.ThunkState m a -> ThSt.ThunkState -> m a
evalStateT' = evalStateT

testThunkNormalizeSt :: String -> Either String (Either ExtendedLambda ExtendedLambda)
testThunkNormalizeSt s = uncurry normalizeSt $ runState (testElParseSt s) 0

testThunkNormalizeST :: String -> Either String (Either ExtendedLambda ExtendedLambda)
testThunkNormalizeST s = uncurry normalizeST $ runState (testElParseSt s) 0

normalizeSt :: ExtendedLambda -> Int -> Either String (Either ExtendedLambda ExtendedLambda)
normalizeSt e i = runExcept $ flip evalStateT' counterEmptyState $ chain e i

normalizeST :: ExtendedLambda -> Int -> Either String (Either ExtendedLambda ExtendedLambda)
normalizeST e i = runExcept $ ThST.evalThunkSTT $ chain e i

testChain :: (MonadThunkState ref m, MonadError String m) => String -> m (Either ExtendedLambda ExtendedLambda)
testChain s = uncurry chain $ runState (testElParseSt s) 0

chain :: (MonadThunkState ref m, MonadError String m) => ExtendedLambda -> Int -> m (Either ExtendedLambda ExtendedLambda)
chain e i = chain' $ evalState (normalizeRecursion e) i

chain' :: (MonadThunkState ref m, MonadError String m) => ExtendedLambda -> m (Either ExtendedLambda ExtendedLambda)
chain' = convertToThunks >=> normalize >=> either (convertFromThunks >=> left) (convertFromThunks >=> right)


normalize :: (MonadThunkState ref m, MonadError String m) => ref -> m (Either ref ref)
normalize = \r -> do
    iT <- convertToThunks elIfTrue
    iF <- convertToThunks elIfFalse
    cL <- convertToThunks elCaseL
    cR <- convertToThunks elCaseR
    bImpl iT iF cL cR r
  where bImpl :: (MonadThunkState ref m, MonadError String m) => ref -> ref -> ref -> ref -> ref -> m (Either ref ref)
        bImpl !ifTrueTh !ifFalseTh !caseL !caseR = impl HM.empty
          where
           impl !m !_thRef = do
               traceM' $ return $ "Digged to thRef " ++ show _thRef ++ ", within context: " ++ (show m)
               _thRef' <- trace' "@@ 0" . joinCtx m =<< getCached _thRef
               if _thRef' /= _thRef
                  then traceM' $ return $ "Merged contexts, new thRef: " ++ show _thRef'
                  else return ()
               repeatNorm' (withCache impl') _thRef'
           impl' !thRef = do
                 encloseCtx thRef
                 propagateCtx thRef
                 propagateCached thRef
                 traceM' $ thShowIdent 0 thRef >>= return . (++) "Traversing to expr = "
                 th <- getThunk thRef
                 let ctx = thContext th
                 case thExpr th of
                     V !v -> let substVar varRef = do
                                   traceM' $ return . (("Substituting to var " ++ v ++ ": ") ++) =<< thShowIdent 0 varRef
                                   varRef' <- trace' "@@ 1" $ joinCtx ctx varRef
                                   right varRef'
                             in case v `HM.lookup` ctx of
                                  Just varRef -> substVar varRef
                                  _ -> left thRef
                     pTh :@ qTh -> do
                        propagateCached pTh
                        propagateCached qTh
                        p <- thExpr <$> getThunk pTh
                        q <- thExpr <$> getThunk qTh
                        pCtx <- thContext <$> getThunk pTh
                        qCtx <- thContext <$> getThunk qTh
                        let digLeft = trace' "digLeft" $ dig alterLeft pTh
                            digRight = trace' "digRight" $ dig alterRight qTh
                            alterLeft !pTh' = updThunk thRef (\s -> s { thExpr = pTh' :@ qTh }) >> right thRef
                            alterRight !qTh' = updThunk thRef (\s -> s { thExpr = pTh :@ qTh' }) >> right thRef
                            dig alter !comp = impl ctx comp >>= either alter' alter
                              where alter' comp' = if comp == comp'
                                                   then left thRef
                                                   else alter comp'
                            synError = throwError . (++) "Can't normalize: " =<< thShowIdent 0 thRef
                        case p of
                          IOp _ -> case q of
                                      (_ :@ _) -> digRight
                                      (V _) -> digRight
                                      (I _) -> digRight
                                      _ -> synError
                          OrdOp _ -> case q of
                                      (_ :@ _) -> digRight
                                      (V _) -> digRight
                                      (I _) -> digRight
                                      _ -> synError
                          If -> case q of
                                  (B b) -> if b
                                              then right ifTrueTh
                                              else right ifFalseTh
                                  (_ :@ _) -> digRight
                                  (V _) -> digRight
                                  e -> synError
                          PrL -> case q of
                                   aTh :~ bTh -> right =<< joinCtx ctx =<< joinCtx qCtx aTh
                                   (_ :@ _) -> digRight
                                   (V _) -> digRight
                                   _ -> synError
                          PrR -> case q of
                                   aTh :~ bTh -> right =<< joinCtx ctx =<< joinCtx qCtx bTh
                                   (_ :@ _) -> digRight
                                   (V _) -> digRight
                                   _ -> synError
                          (Abs v s) -> do
                               qTh' <- trace' "@@ 6" $ joinCtx ctx qTh
                               right =<< joinCtx ctx =<< joinCtx (HM.singleton v qTh') =<< joinCtx pCtx s
                          Y -> do
                               restTh <- newThunk th { thContext = HM.empty }
                               updThunk thRef (\s -> s { thExpr = qTh :@ restTh })
                               right thRef
                          Case -> case q of
                                   qlTh :@ qrTh -> do propagateCached qlTh
                                                      ql <- thExpr <$> getThunk qlTh
                                                      case ql of
                                                        InL -> do
                                                           updThunk thRef (\s -> s { thExpr = caseL :@ qrTh })
                                                           right thRef
                                                        InR -> do
                                                           updThunk thRef (\s -> s { thExpr = caseR :@ qrTh })
                                                           right thRef
                                                        (_ :@ _) -> digRight
                                                        (V _) -> digRight
                                                        _ -> synError
                                   _ -> synError
                          plTh :@ prTh -> do propagateCached plTh
                                             propagateCached prTh
                                             pl <- thExpr <$> getThunk plTh
                                             pr <- thExpr <$> getThunk prTh
                                             case (pl, pr, q) of
                                              (IOp op, I i, I j) -> do
                                                updThunk thRef (\s -> s { thExpr = I (iop op i j)
                                                                        , thContext = HM.empty })
                                                right thRef
                                              (IOp _, I _, (_ :@ _)) -> digRight
                                              (IOp _, I _, V _) -> digRight
                                              (IOp _, I _, _) -> synError
                                              (OrdOp op, I i, I j) -> do
                                                updThunk thRef (\s -> s { thExpr = B (ordOp op i j)
                                                                        , thContext = HM.empty })
                                                right thRef
                                              (OrdOp _, I _, (_ :@ _)) -> digRight
                                              (OrdOp _, I _, V _) -> digRight
                                              (OrdOp _, I _, _) -> synError
                                              _ -> digLeft
                          _ -> digLeft
                     _ -> left thRef
