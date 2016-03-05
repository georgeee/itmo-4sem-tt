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

testThunkNormalizeSt :: Bool -> String -> Either String ExtendedLambda
testThunkNormalizeSt toNF s = uncurry (normalizeSt toNF) $ runState (testElParseSt s) 0

testThunkNormalizeST :: Bool -> String -> Either String ExtendedLambda
testThunkNormalizeST toNF s = uncurry (normalizeST toNF) $ runState (testElParseSt s) 0

normalizeSt :: Bool -> ExtendedLambda -> Int -> Either String ExtendedLambda
normalizeSt toNF e i = runExcept $ flip evalStateT' counterEmptyState $ chain toNF e i

normalizeST :: Bool -> ExtendedLambda -> Int -> Either String ExtendedLambda
normalizeST toNF e i = runExcept $ ThST.evalThunkSTT $ chain toNF e i

chain :: (MonadThunkState ref m, MonadError String m) => Bool -> ExtendedLambda -> Int -> m ExtendedLambda
chain toNF e i = chain' toNF $ evalState (normalizeRecursion e) i

chain' :: (MonadThunkState ref m, MonadError String m) => Bool -> ExtendedLambda -> m ExtendedLambda
chain' toNF  = convertToThunks >=> normalize toNF >=> convertFromThunks

stripNormalized :: (MonadThunkState ref m, MonadError String m) => ref -> m ref
stripNormalized thRef = do
  encloseCtx thRef
  propagateCtx thRef
  propagateCached thRef
  --th <- getThunk thRef
  --e' <- case thExpr th of
  --   a :~ b -> (:~) <$> stripNormalized a <*> stripNormalized b
  --   a :@ b -> (:@) <$> stripNormalized a <*> stripNormalized b
  --   Abs v s -> Abs v <$> stripNormalized s
  --   e -> return e
  --updThunk thRef (\s -> s { thNormalized = Nothing, thExpr = e' })
  return thRef

normalize :: (MonadThunkState ref m, MonadError String m) => Bool -> ref -> m ref
normalize toNF = \r -> do
    iT <- convertToThunks elIfTrue
    iF <- convertToThunks elIfFalse
    cL <- convertToThunks elCaseL
    cR <- convertToThunks elCaseR
    bImpl iT iF cL cR r
  where bImpl :: (MonadThunkState ref m, MonadError String m) => ref -> ref -> ref -> ref -> ref -> m ref
        bImpl !ifTrueTh !ifFalseTh !caseL !caseR = if toNF then implNF else implHNF
          where
           getThref !m !_thRef = do
               _thRef' <- joinCtx m =<< getCached _thRef
               if _thRef' /= _thRef
                  then traceM' $ return $ "Merged contexts, new thRef: " ++ show _thRef'
                  else return ()
               return _thRef'
           impl !m !_thRef = do
               traceM' $ return $ "Digged to thRef " ++ show _thRef ++ ", within context: " ++ (show m)
               thRef <- getThref m _thRef
               th <- getThunk thRef
               repeatNorm' (withCache $ impl') thRef
           implHNF e = either id id <$> impl LHM.empty e
           implNF = implHNF >=> getCached >=> stripNormalized
                      >=> \thRef' -> do
                             th <- getThunk thRef'
                             e' <- case thExpr th of
                               a :~ b -> (:~) <$> implNF a <*> implNF b
                               a :@ b -> (:@) <$> implNF a <*> implNF b
                               Abs v s -> Abs v <$> implNF s
                               e -> return e
                             updThunk thRef' (\s -> s { thExpr = e' })
                             stripNormalized thRef'
           impl' !thRef = do
                 encloseCtx thRef
                 propagateCtx thRef
                 propagateCached thRef
                 traceM' $ thShowIdent 0 thRef >>= return . (++) "Traversing to expr = "
                 th <- getThunk thRef
                 let ctx = thContext th
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
                        let digLeft = trace' "digLeft" $ dig alterLeft pTh
                            digRight = trace' "digRight" $ dig alterRight qTh
                            alterLeft !pTh' = upd right (pTh' :@ qTh)
                            alterRight !qTh' = upd right (pTh :@ qTh')
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
                                   aTh :~ _ -> right
                                            =<< joinCtx qCtx aTh
                                   (_ :@ _) -> digRight
                                   (V _) -> digRight
                                   _ -> synError
                          PrR -> case q of
                                   _ :~ bTh -> right
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
                                   V _ -> digRight
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
                                              _ -> digLeft
                          _ -> digLeft
                     _ -> left thRef
