{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances, BangPatterns,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module ExtendedLambda.Thunk.Normalization where

import Data.Either.Combinators
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
import qualified Data.LinkedHashMap.IntMap as LHM

evalStateT' :: Monad m => StateT ThSt.ThunkState m a -> ThSt.ThunkState -> m a
evalStateT' = evalStateT

testThunkNormalizeSt :: Bool -> String -> Either String (Either ExtendedLambda ExtendedLambda)
testThunkNormalizeSt toNF s = uncurry (normalizeSt toNF) $ runState (testElParseSt s) 0

testThunkNormalizeST :: Bool -> String -> Either String (Either ExtendedLambda ExtendedLambda)
testThunkNormalizeST toNF s = uncurry (normalizeST toNF) $ runState (testElParseSt s) 0

normalizeSt :: Bool -> ExtendedLambda -> Int -> Either String (Either ExtendedLambda ExtendedLambda)
normalizeSt toNF e i = runExcept $ flip evalStateT' counterEmptyState $ chain toNF e i

normalizeST :: Bool -> ExtendedLambda -> Int -> Either String (Either ExtendedLambda ExtendedLambda)
normalizeST toNF e i = runExcept $ ThST.evalThunkSTT $ chain toNF e i

chain :: (MonadThunkState ref m, MonadError String m) => Bool -> ExtendedLambda -> Int -> m (Either ExtendedLambda ExtendedLambda)
chain toNF e i = chain' toNF $ evalState (normalizeRecursion e) i

chain' :: (MonadThunkState ref m, MonadError String m) => Bool -> ExtendedLambda -> m (Either ExtendedLambda ExtendedLambda)
chain' toNF  = convertToThunks >=> normalize toNF >=> either (convertFromThunks >=> left) (convertFromThunks >=> right)

normalize :: (MonadThunkState ref m, MonadError String m) => Bool -> ref -> m (Either ref ref)
normalize toNF = \r -> do
    iT <- convertToThunks elIfTrue
    iF <- convertToThunks elIfFalse
    cL <- convertToThunks elCaseL
    cR <- convertToThunks elCaseR
    bImpl iT iF cL cR r
  where bImpl :: (MonadThunkState ref m, MonadError String m) => ref -> ref -> ref -> ref -> ref -> m (Either ref ref)
        bImpl !ifTrueTh !ifFalseTh !caseL !caseR = impl True LHM.empty
          where
           getThref !m !_thRef = do
               _thRef' <- joinCtx m =<< getCached _thRef
               if _thRef' /= _thRef
                  then traceM' $ return $ "Merged contexts, new thRef: " ++ show _thRef'
                  else return ()
               return _thRef'
           impl lb !m !_thRef = do
               traceM' $ return $ "Digged to thRef " ++ show _thRef ++ ", within context: " ++ (show m)
               thRef <- getThref m _thRef
               th <- getThunk thRef
               if lb && not (thLb th)
                  then trace' ("Resetting cache for lb " ++ show thRef) $ updThunk thRef (\s -> s { thNormalized = Nothing, thLb = True })
                  else return ()
               repeatNorm' (withCache $ impl' lb) thRef
           impl' lb !thRef = do
                 encloseCtx thRef
                 propagateCtx thRef
                 propagateCached thRef
                 traceM' $ thShowIdent 0 thRef >>= return . (++) "Traversing to expr = "
                 th <- getThunk thRef
                 let ctx = thContext th
                     digBoth cons pTh qTh implL implR = implL ctx pTh >>= \c -> implR ctx qTh >>= res c
                        where res (Right x) yE = rRes x $ either id id yE
                              res (Left x) yE = either (lRes x) (rRes x) yE
                              rRes pTh' qTh' = upd right $ cons pTh' qTh'
                              lRes pTh' qTh' = if pTh /= pTh' || qTh /= qTh'
                                                  then upd right $ cons pTh' qTh'
                                                  else left thRef
                     upd r e = updThunk thRef (\s -> s { thExpr = e }) >> r thRef
                 case thExpr th of
                     V !v -> let substVar varRef = do
                                   traceM' $ return . (("Substituting to var " ++ v ++ ": ") ++) =<< thShowIdent 0 varRef
                                   varRef' <- joinCtx ctx varRef
                                   right varRef'
                             in case v `LHM.lookup` ctx of
                                  Just varRef -> substVar varRef
                                  _ -> left thRef
                     pTh :@ qTh -> do
                        propagateCached pTh
                        propagateCached qTh
                        p <- thExpr <$> getThunk pTh
                        q <- thExpr <$> getThunk qTh
                        pCtx <- thContext <$> getThunk pTh
                        qCtx <- thContext <$> getThunk qTh
                        let digLeft = trace' "digLeft" $ dig False alterLeft pTh
                            digRight = trace' "digRight" $ dig False alterRight qTh
                            alterLeft !pTh' = upd right (pTh' :@ qTh)
                            alterRight !qTh' = upd right (pTh :@ qTh')
                            dig lb alter !comp = impl lb ctx comp >>= either alter' alter
                              where alter' comp' = if comp == comp'
                                                      then left thRef
                                                      else alter comp'
                            digBoth' = digLeft >>= either (const $ dig True alterRight qTh) right
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
                                   aTh :~ _ -> right
                                            -- =<< joinCtx ctx
                                            =<< joinCtx qCtx aTh
                                   (_ :@ _) -> digRight
                                   (V _) -> digRight
                                   _ -> synError
                          PrR -> case q of
                                   _ :~ bTh -> right
                                        -- =<< joinCtx ctx
                                        =<< joinCtx qCtx bTh
                                   (_ :@ _) -> digRight
                                   (V _) -> digRight
                                   _ -> synError
                          (Abs v s) -> right =<< joinCtx pCtx =<< joinCtx (LHM.singleton v qTh) s
                          Y -> do
                             restTh <- newThunk th
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
                          _ :~ _ -> synError
                          plTh :@ prTh -> do propagateCached plTh
                                             propagateCached prTh
                                             pl <- thExpr <$> getThunk plTh
                                             pr <- thExpr <$> getThunk prTh
                                             case (pl, pr, q) of
                                              (IOp op, I i, I j) -> do
                                                updThunk thRef (\s -> s { thExpr = I (iop op i j)
                                                                        , thContext = LHM.empty })
                                                right thRef
                                              (IOp _, I _, (_ :@ _)) -> digRight
                                              (IOp _, I _, V _) -> digRight
                                              (IOp _, I _, _) -> synError
                                              (OrdOp op, I i, I j) -> do
                                                updThunk thRef (\s -> s { thExpr = B (ordOp op i j)
                                                                        , thContext = LHM.empty })
                                                right thRef
                                              (OrdOp _, I _, (_ :@ _)) -> digRight
                                              (OrdOp _, I _, V _) -> digRight
                                              (OrdOp _, I _, _) -> synError
                                              _ -> if toNF && lb then digBoth' else digLeft
                          _ -> if toNF && lb then digBoth' else digLeft
                     pTh :~ qTh -> if lb
                                      then digBoth (:~) pTh qTh (impl True) (impl True)
                                      else left thRef
                     Abs v e -> if toNF && lb
                                   then do
                                     e' <- impl True ctx e
                                     case e' of
                                       Left e'' -> if e'' /= e
                                                      then upd right $ Abs v e''
                                                      else left thRef
                                       Right e'' -> upd right $ Abs v e''
                                   else left thRef
                     _ -> left thRef
