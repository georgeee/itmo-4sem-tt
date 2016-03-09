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
import Data.Foldable as F
import Common
import Control.Monad.Error.Class (catchError, MonadError, throwError)
import Control.Monad.Trans.Either hiding (left, right)
import Control.Monad.Trans.Except (Except, runExcept)
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS
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

traceM'' :: Monad m => m String -> m ()
traceM'' = const $ return ()
trace'' x y = y
--traceM'' = (=<<) traceM
--trace'' = trace

renameVars :: (MonadThunkState ref m, MonadError String m) => ref -> m ref
renameVars = impl HM.empty
  where impl fvs thRef = do
            th <- getThunk thRef
            e' <- case thExpr th of
              (l :~ r) -> (:~) <$> impl fvs l <*> impl fvs r
              (l :@ r) -> (:@) <$> impl fvs l <*> impl fvs r
              (Abs v e) -> Abs v' <$> impl fvs' e
                where (v', fvs') = rV v fvs
              (V v) -> pure $ V $ gV v fvs
              e -> pure e
            ctx' <- traverse (impl fvs) (thContext th)
            updThunk thRef (\s -> s { thExpr = e', thContext = ctx' })
            return thRef
        gV :: Var -> HM.HashMap Var Int -> Var
        gV v fvs = case v `HM.lookup` fvs of
                         Just 0 -> v
                         Just i -> "_" ++ v ++ show (i - 1)
                         _ -> v
        rV :: Var -> HM.HashMap Var Int -> (Var, HM.HashMap Var Int)
        rV v fvs = case v `HM.lookup` fvs of
                        Just i -> ("_" ++ v ++ show i, HM.insert v (i+1) fvs)
                        _ -> (v, HM.insert v 0 fvs)

propagateRecursive :: (MonadThunkState ref m, MonadError String m) => ref -> m ref
propagateRecursive = impl
  where impl = propagateCtx >=> \thRef -> do
            b' <- thExpr <$> getThunk thRef >>= impl'
            updThunk thRef (\s -> s { thExpr = b' })
            return thRef
        impl' (l :~ r) = (:~) <$> impl l <*> impl r
        impl' (l :@ r) = (:@) <$> impl l <*> impl r
        impl' (Abs v e) = Abs v <$> impl e
        impl' e = return e

normalize :: (MonadThunkState ref m, MonadError String m) => Bool -> ref -> m ref
normalize toNF = \r -> do
    iT <- convertToThunks elIfTrue
    iF <- convertToThunks elIfFalse
    cL <- convertToThunks elCaseL
    cR <- convertToThunks elCaseR
    bImpl iT iF cL cR r
  where bImpl :: (MonadThunkState ref m, MonadError String m) => ref -> ref -> ref -> ref -> ref -> m ref
        bImpl !ifTrueTh !ifFalseTh !caseL !caseR = if toNF then implNF >=> renameVars >=> propagateRecursive else implHNF
          where
           impl = getCached >=> repeatNorm' (withCache impl')

           prBeforeHNF thRef = do traceM''$ (++) "Expr for HNF: " <$> thShowIdent 0 thRef
                                  return thRef
           implHNF = prBeforeHNF >=> propagateCtx >=> \_thRef -> do
              traceM''$ (++) "Expr for HNF (ctx propagated): " <$> thShowIdent 0 _thRef
              _th <- getThunk _thRef
              let fvs = thFree _th
              repls <- mapM (\v -> (,) v . (++) "__v" . show <$> nextThunkId) $ HS.toList fvs
              ctx <- foldM (\b (v, v') -> flip (LHM.insert v) b <$> genNewVarThref v') (thContext _th) repls
              thRef <- joinCtx ctx _thRef

              traceM''$ (++) "Prepared for HNF: " <$> thShowIdent 0 thRef
              _thRef' <- either id id <$> impl thRef >>= propagateCtx
              traceM''$ (++) "After HNF: " <$> thShowIdent 0 _thRef'

              _th' <- getThunk _thRef'
              ctx'' <- foldM (\b (v, v') -> flip (LHM.insert v') b <$> genNewVarThref v) (thContext _th') repls
              thRef' <- joinCtx ctx'' _thRef'
              traceM''$ (++) "Normalized to HNF: " <$> thShowIdent 0 thRef'
              return thRef'

           genNewVarThref v' = newThunk Thunk { thId = undefined
                                              , thFree = undefined
                                              , thNormalized = undefined
                                              , thExpr = V v'
                                              , thContext = LHM.empty
                                              }
           implNF = implHNF >=> getCached
                      >=> \thRef' -> do
                             propagateCached thRef'
                             traceM''$ (++) "Normalized to HNF, ctx propagated: " <$> thShowIdent 0 thRef'
                             th <- getThunk thRef'
                             e' <- case thExpr th of
                               a :~ b -> (:~) <$> implNF a <*> implNF b
                               a :@ b -> (:@) <$> implNF a <*> implNF b
                               Abs v s -> Abs v <$> implNF s
                               e -> return e
                             updThunk thRef' (\s -> s { thExpr = e' })
                             traceM''$ (++) "Normalized to NF: " <$> thShowIdent 0 thRef'
                             return thRef'
                             --thRef'' <- propagateCtx thRef'
                             --traceM''$ (++) "Normalized to NF, ctx propagated: " <$> thShowIdent 0 thRef''
                             --return thRef''
           impl' = propagateCtx >=> \thRef -> do
                 traceM' $ (++) "Traversing to expr = " <$> thShowIdent 0 thRef
                 th <- getThunk thRef
                 if F.null (thContext th)
                    then return ()
                    else throwError . (++) "Invalid branch: ctx isn't propagated properly, " =<< thShowIdent 0 thRef
                 let upd r e = updThunk thRef (\s -> s { thExpr = e }) >> r thRef
                     synError = throwError . (++) "Can't normalize: " =<< thShowIdent 0 thRef
                 case thExpr th of
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
                            dig alter !comp = impl comp >>= either alter' alter
                              where alter' comp' = if comp == comp'
                                                      then left thRef
                                                      else alter comp'
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
                                   qlTh :@ qrTh -> do
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
                          plTh :@ prTh -> do pl <- thExpr <$> getThunk plTh
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
