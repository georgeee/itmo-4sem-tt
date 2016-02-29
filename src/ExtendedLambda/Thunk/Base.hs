{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module ExtendedLambda.Thunk.Base where

import Control.Monad.Trans.Reader (ReaderT, runReaderT)
import Control.Monad.Error.Class (catchError)
import Control.Monad.Trans.Either (left, EitherT)
import Control.Monad.Trans.Except (throwE)
import Control.Monad.Trans.Class (lift)
import Data.List
import Debug.Trace
import Common
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS
import qualified Data.LinkedHashMap.IntMap as LHM
import ExtendedLambda.Types
import ExtendedLambda.Base
import Data.Hashable
import Control.Monad

traceM' :: Monad m => m String -> m ()
traceM' = const $ return ()
trace' x y = y
--traceM' = (=<<) traceM
--trace' = trace

type ThunkContext ref = HM.HashMap Var ref

type ThunkId = Int

data Thunk ref = Thunk { thId :: ThunkId
                       , thExpr :: ExtendedLambdaBase ref
                       , thContext :: ThunkContext ref
                       , thFree :: HS.HashSet Var
                       , thNormalized :: Maybe ref
                       }

class Monad m => MonadThunkId m where
  nextThunkId :: m ThunkId

class (MonadThunkId m, Show ref, Eq ref) => MonadThunkState ref m where
  updThunk :: ref -> (Thunk ref -> Thunk ref) -> m ()
  addThunk :: Thunk ref -> m ref
  getThunk :: ref -> m (Thunk ref)

instance MonadThunkId m => MonadThunkId (ReaderT a m) where
  nextThunkId = lift nextThunkId
instance MonadThunkState ref m => MonadThunkState ref (ReaderT a m) where
  getThunk = lift . getThunk
  updThunk r = lift . updThunk r
  addThunk = lift . addThunk
instance MonadThunkId m => MonadThunkId (EitherT a m) where
  nextThunkId = lift nextThunkId
instance MonadThunkState ref m => MonadThunkState ref (EitherT a m) where
  getThunk = lift . getThunk
  updThunk r = lift . updThunk r
  addThunk = lift . addThunk

newThunk :: MonadThunkState ref m => Thunk ref -> m ref
newThunk th = do thId <- nextThunkId
                 th' <- computeThunkFV th
                 addThunk th' { thId = thId, thNormalized = Nothing }


thNormalized' :: MonadThunkState ref m => ref -> m (Maybe ref)
thNormalized' = fmap thNormalized . getThunk

-- set thRef' as normalized for thRef, returns thRef'
setThNormalized :: MonadThunkState ref m => ref -> ref -> m ref
setThNormalized thRef thRef' = do
     updThunk thRef (\s -> s { thNormalized = Just thRef' })
     traceM' $ (++) ("-- " ++ show thRef ++ " normalized to ") <$> thShowIdent 0 thRef'
     return thRef'

getCached :: MonadThunkState ref m => ref -> m ref
getCached thRef = maybe thRef id <$> thNormalized' thRef

withCache :: (MonadThunkState ref n) => (ref -> EitherT ref n ref) -> ref -> EitherT ref n ref
withCache action thRef = logStepping thRef >> thNormalized' thRef >>= impl1
  where impl1 Nothing = action' thRef `catchError` (setThNormalized thRef >=> left)
        impl1 (Just thRef') = if thRef == thRef'
                                 then trace' ("-- " ++ show thRef ++ " already normalized ") $ left thRef
                                 else impl2 thRef' >>= setThNormalized thRef
        impl2 thRef' = logStepping thRef' >> thNormalized' thRef' >>= impl3 >>= setThNormalized thRef'
            where impl3 = maybe (action' thRef' `catchError` return) impl2
        logStepping thRef = trace' ("-- stepping into " ++ show thRef) $ return thRef
        logRepeatting thRef = trace' ("-- repeatting " ++ show thRef) $ return thRef
        --action' - action, executed repeatedly with same thRef (till first left)
        action' thRef = action thRef >>= toRight . action'' thRef
        action'' thRef = setThNormalized thRef >=> \thRef' -> action thRef' >>= logRepeatting >>= action'' thRef'



ctxInnerFV :: MonadThunkState ref m => ThunkContext ref -> m (HS.HashSet Var)
ctxInnerFV = foldM (\b a -> HS.union b <$> thFree' a) HS.empty . HM.elems

encloseCtx :: MonadThunkState ref m => ref -> m ()
encloseCtx thRef = do
      th <- getThunk thRef
      baseFV <- baseToFreeVars $ thExpr th
      let ctx = thContext th
      ctx' <- traverse (joinCtx ctx) ctx
      let ctx'' = HM.intersectionWith (const id) (HS.toMap baseFV) ctx'
      updThunk thRef (\s -> s { thContext = ctx'' })

-- thRef's ctx entries are assummed to be enclosed
propagateCtx :: MonadThunkState ref m => ref -> m ()
propagateCtx thRef = do
  th <- getThunk thRef
  base' <- propagateCtxToBase (thContext th) (thExpr th)
  case base' of
    Just e -> updThunk thRef (\s -> s { thExpr = e, thContext = HM.empty })
    _ -> return ()

joinCtx :: MonadThunkState ref m => ThunkContext ref -> ref -> m ref
joinCtx ctx thRef = do
      fv <- thFree' thRef
      ctxFV <- ctxInnerFV (HM.intersectionWith (const id) (HS.toMap fv) ctx)
      let fvMs = HS.toMap $ HS.union ctxFV fv
          ctx' = HM.intersectionWith (const id) fvMs ctx
      if HM.null ctx'
         then return thRef
         else do
            traceM' $ do s' <- thShowIdent 0 thRef
                         c' <- showLBs 0 ctx'
                         return $ "joinCtx " ++ show c' ++ " " ++ s'
            th <- getThunk thRef
            let l1 = HM.toList ctx'
                l2 = HM.toList $ thContext th
            newCtx <- HM.fromList <$> normalizeCtx HS.empty HM.empty (reverse $ l1 ++ l2)
            trace' "Exitting joinCtx" $ newThunk $ th { thContext = newCtx }

normalizeCtx :: MonadThunkState ref m => HS.HashSet Var -> ThunkContext ref -> [(Var, ref)] -> m [(Var, ref)]
normalizeCtx _ rCtx [] = return []
normalizeCtx vs rCtx ((v, e) : as) = if v `HS.member` vs
                                        then normalizeCtx vs (HM.insert v e rCtx) as
                                        else (:) . (,) v <$> joinCtx rCtx e
                                                         <*> normalizeCtx (HS.insert v vs) rCtx as


joinCtxM :: MonadThunkState ref m => ThunkContext ref -> ThunkContext ref -> m (ThunkContext ref)
joinCtxM m ctx = HM.union ctx <$> mapM (joinCtx m) (HM.difference m ctx)

thShowIdent' :: MonadThunkState ref m => Int -> ExtendedLambdaBase ref -> m String
thShowIdent' _ (I x) = return $ show x
thShowIdent' _ (B b) = return $ if b then "T" else "F"
thShowIdent' _ Y = return "Y"
thShowIdent' _ PrL = return "PrL"
thShowIdent' _ PrR = return "PrR"
thShowIdent' _ InL = return "InL"
thShowIdent' _ InR = return "InR"
thShowIdent' _ Case = return "Case"
thShowIdent' _ If = return "If"
thShowIdent' _ (IOp Add) = return "Plus"
thShowIdent' _ (IOp Subtract) = return "Minus"
thShowIdent' _ (OrdOp EQ) = return "Eq"
thShowIdent' _ (OrdOp LT) = return "Lt"
thShowIdent' _ (OrdOp GT) = return "Gt"
thShowIdent' i (l :~ r) = let i' = i + 1 in do
                          l' <- thShowIdent i' l
                          r' <- thShowIdent i' r
                          return $ "<" ++ l' ++ ", " ++ r' ++ ">"
thShowIdent' i (Abs v e) = let i' = i + 1 in do
                            e' <- thShowIdent i' e
                            return $ "(\\" ++ v ++ ". " ++ e' ++ ")"
thShowIdent' i (l :@ r) = let i' = i + 1 in do
                        l' <- thShowIdent i' l
                        r' <- show' i' r
                        return $ l' ++ " " ++ r'
  where
    show' :: MonadThunkState ref m => Int -> ref -> m String
    show' i r = do
        el <- thExpr <$> getThunk r
        case el of
            (_ :@ _) -> (\x -> "(" ++ x ++ ")") <$> thShowIdent i r
            _ -> thShowIdent i r
thShowIdent' _ (V v) = return v

thShowIdent :: MonadThunkState ref m => Int -> ref -> m String
thShowIdent i thRef = do th <- getThunk thRef
                         let bs = thContext th
                             t = thExpr th
                         if HM.null bs then ((show thRef ++ ":") ++) <$> thShowIdent' i t else let i' = i + 1 in do
                            lbs <- showLBs i' bs
                            t' <- thShowIdent' i' t
                            return $ concat [ (show thRef ++ ":")
                                            , "\n" ++ (sps $ i * 2) ++ "(let " ++ (intercalate (",\n" ++ (sps $ i * 2 + 4)) lbs)
                                            , "\n" ++ (sps $ i' * 2 - 1) ++ "in " ++ t' ++ ")"
                                            ]
showLBs :: MonadThunkState ref m => Int -> ThunkContext ref -> m [String]
showLBs i = mapM (\(v, s) -> ((v ++ " = ") ++) <$> thShowIdent i s) . HM.toList

p i s = (replicate (i*2) ' ') ++ s
sps = flip replicate ' '


convertToThunks :: MonadThunkState ref m => ExtendedLambda -> m ref
convertToThunks (ctx ::= e) = do thId <- nextThunkId
                                 base <- convertBase e
                                 ctx' <- convertCtx ctx
                                 fv <- computeThunkFV' base ctx'
                                 let thunk = Thunk { thId = thId
                                                   , thExpr = base
                                                   , thContext = ctx'
                                                   , thFree = fv
                                                   , thNormalized = Nothing
                                                   }
                                 addThunk thunk

convertBase :: MonadThunkState ref m => ExtendedLambdaBase ExtendedLambda -> m (ExtendedLambdaBase ref)
convertBase (I i) = return $ I i
convertBase (B b) = return $ B b
convertBase Y = return $ Y
convertBase PrL = return $ PrL
convertBase PrR = return $ PrR
convertBase InL = return $ InL
convertBase InR = return $ InR
convertBase Case = return $ Case
convertBase If = return $ If
convertBase (IOp op) = return $ IOp op
convertBase (OrdOp ord) = return $ OrdOp ord
convertBase (l :~ r) = (:~) <$> convertToThunks l <*> convertToThunks r
convertBase (l :@ r) = (:@) <$> convertToThunks l <*> convertToThunks r
convertBase (Abs v e) = Abs v <$> convertToThunks e
convertBase (V v) = return $ V v

computeThunkFV :: MonadThunkState ref m => Thunk ref -> m (Thunk ref)
computeThunkFV th = (\fv -> th { thFree = fv }) <$> computeThunkFV' (thExpr th) (thContext th)

computeThunkFV' :: MonadThunkState ref m => ExtendedLambdaBase ref -> ThunkContext ref -> m (HS.HashSet Var)
computeThunkFV' base ctx = do
    ctxFV <- ctxInnerFV ctx
    baseFV <- baseToFreeVars base
    return $ (ctxFV `HS.union` baseFV) `HS.difference` ctxVars
  where ctxVars = HS.fromList $ HM.keys ctx

propagateCached :: MonadThunkState ref m => ref -> m ()
propagateCached thRef = thExpr <$> getThunk thRef >>= impl >>= \b -> updThunk thRef (\s -> s { thExpr = b })
  where
    impl :: MonadThunkState ref m => ExtendedLambdaBase ref -> m (ExtendedLambdaBase ref)
    impl (l :~ r) = impl2 l r (:~)
    impl (l :@ r) = impl2 l r (:@)
    impl (Abs v e) = Abs v <$> getCached e
    impl e = return e
    impl2 :: MonadThunkState ref m => ref -> ref -> (ref -> ref -> ExtendedLambdaBase ref) -> m (ExtendedLambdaBase ref)
    impl2 l r f = f <$> getCached l <*> getCached r

thFree' :: MonadThunkState ref m => ref -> m (HS.HashSet Var)
thFree' thRef = thFree <$> getThunk thRef

-- ctx entries are assummed to be enclosed
propagateCtxToBase :: MonadThunkState ref m => ThunkContext ref -> ExtendedLambdaBase ref -> m (Maybe (ExtendedLambdaBase ref))
propagateCtxToBase ctx (l :~ r)  = Just <$> ( (:~) <$> joinCtx ctx l <*> joinCtx ctx r )
propagateCtxToBase ctx (l :@ r)  = Just <$> ( (:@) <$> joinCtx ctx l <*> joinCtx ctx r )
propagateCtxToBase ctx (Abs v e) = Just <$> ( Abs v <$> joinCtx (HM.delete v ctx) e    )
propagateCtxToBase _ _ = return Nothing

baseToFreeVars :: MonadThunkState ref m => ExtendedLambdaBase ref -> m (HS.HashSet Var)
baseToFreeVars (l :~ r) = HS.union <$> thFree' l <*> thFree' r
baseToFreeVars (l :@ r) = HS.union <$> thFree' l <*> thFree' r
baseToFreeVars (Abs v e) = HS.delete v <$> thFree' e
baseToFreeVars (V v) = return $ HS.singleton v
baseToFreeVars _ = return HS.empty

convertCtx :: MonadThunkState ref m => ELContext -> m (HM.HashMap Var ref)
convertCtx ctx = HM.fromList <$> mapM (\(v, e) -> (,) v <$> convertToThunks e) (LHM.toList ctx)

