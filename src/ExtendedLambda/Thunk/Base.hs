{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module ExtendedLambda.Thunk.Base where

import Data.List
import Control.Monad.State.Class
import Debug.Trace
import Common
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS
import qualified Data.LinkedHashMap.IntMap as LHM
import ExtendedLambda.Types
import ExtendedLambda.Base
import Data.Hashable
import Control.Monad.State.Strict

traceM' :: Monad m => m String -> m ()
--traceM' = const $ return ()
traceM' = (=<<) traceM
--trace' x y = y
trace' = trace

newtype ThunkRef = ThunkRef Int
  deriving (Eq, Hashable)

instance Show ThunkRef where
  show (ThunkRef i) = '#' : show i

type ThunkContext = HM.HashMap Var ThunkRef

data Thunk = Thunk { thId :: ThunkRef
                   , thExpr :: ExtendedLambdaBase ThunkRef
                   , thCounter :: Int
                   , thContext :: ThunkContext
                   , thFree :: HS.HashSet Var
                   , thNormalized :: Bool
                   }

data ThunkState = ThunkState { thunks :: HM.HashMap ThunkRef Thunk
                             , idCounter :: Int
                             , ifTrueTh :: ThunkRef
                             , ifFalseTh :: ThunkRef
                             , caseL :: ThunkRef
                             , caseR :: ThunkRef
                             , redirects :: HM.HashMap ThunkRef (Maybe ThunkRef)
                             }
initState = execState initiateThunkState $ ThunkState { thunks = HM.empty
                       , idCounter = 0
                       , ifTrueTh = undefined
                       , ifFalseTh = undefined
                       , caseL = undefined
                       , caseR = undefined
                       }

initiateThunkState :: MonadState ThunkState m => m ()
initiateThunkState = do
                        e1 <- convertToThunks elIfTrue
                        e2 <- convertToThunks elIfFalse
                        e3 <- convertToThunks elCaseL
                        e4 <- convertToThunks elCaseR
                        get >>= \st -> put st { ifTrueTh = e1
                                              , ifFalseTh = e2
                                              , caseL = e3
                                              , caseR = e4
                                              }


instance CounterBasedState ThunkState where
  counterNext s = let i = idCounter s in (i, s { idCounter = i + 1 })
  counterEmptyState = initState

ctxInnerFV :: MonadState ThunkState m => ThunkContext -> m (HS.HashSet Var)
ctxInnerFV = foldM (\b a -> HS.union b <$> thFree' a) HS.empty . HM.elems

encloseCtx :: MonadState ThunkState m => ThunkRef -> m ()
encloseCtx thRef = do
      th <- getThunk thRef
      baseFV <- baseToFreeVars $ thExpr th
      let ctx = thContext th
      ctx' <- traverse (joinCtx ctx) ctx
      let ctx'' = HM.intersectionWith (const id) (HS.toMap baseFV) ctx'
      updThunk thRef (\s -> s { thContext = ctx'' })


-- joinCtx doesn't obtain ctx's thRefs (i.e. assuming they're properly obtained already)
joinCtx :: MonadState ThunkState m => ThunkContext -> ThunkRef -> m ThunkRef
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
            release thRef
            newThunk $ th { thContext = newCtx }

normalizeCtx _ rCtx [] = mapM release rCtx >> return []
normalizeCtx vs rCtx ((v, e) : as) = if v `HS.member` vs
                                        then do case v `HM.lookup` rCtx of
                                                     Just e' -> release e'
                                                     _ -> return ()
                                                normalizeCtx vs (HM.insert v e rCtx) as
                                        else (:) . (,) v <$> (mapM obtain rCtx >> joinCtx rCtx e)
                                                         <*> normalizeCtx (HS.insert v vs) rCtx as


joinCtxM :: MonadState ThunkState m => ThunkContext -> ThunkContext -> m ThunkContext
joinCtxM m ctx = HM.union ctx <$> mapM (joinCtx m) (HM.difference m ctx)

thShowIdent' :: MonadState ThunkState m => Int -> ExtendedLambdaBase ThunkRef -> m String
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
  where show' i r = do el <- getThunkExpr r
                       case el of
                         (_ :@ _) -> (\x -> "(" ++ x ++ ")") <$> thShowIdent i r
                         _ -> thShowIdent i r
thShowIdent' _ (V v) = return v

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
showLBs i = mapM (\(v, s) -> ((v ++ " = ") ++) <$> thShowIdent i s) . HM.toList

p i s = (replicate (i*2) ' ') ++ s
sps = flip replicate ' '

updThunks f = modify $ \st -> st { thunks = f $ thunks st }
getThunk thRef = gets ((HM.! thRef) . thunks)
updThunk thRef f = updThunks $ \ths -> HM.insert thRef (f $ ths HM.! thRef) ths
getThunkExpr thRef = gets (thExpr . (HM.! thRef) . thunks)
--newThunk th = ThunkRef <$> freshId' >>= \thRef -> updThunks (HM.insert thRef th { thId = thRef, thCounter = 1 }) >> return thRef
newThunk th = do thRef <- ThunkRef <$> freshId'
                 th' <- computeThunkFV th
                 updThunks (HM.insert thRef th' { thId = thRef, thCounter = 1, thNormalized = False })
                 return thRef

release :: MonadState ThunkState m => ThunkRef -> m ()
release thRef = return ()
--release thRef = updThunks $ \ths -> let th = ths HM.! thRef
--                                     in if thCounter th == 1
--                                           then HM.delete thRef ths
--                                           else HM.insert thRef th { thCounter = thCounter th - 1 } ths

obtain :: MonadState ThunkState m => ThunkRef -> m ThunkRef
obtain thRef = updThunk thRef (\th -> th { thCounter = thCounter th + 1 }) >> return thRef

convertToThunks :: MonadState ThunkState m => ExtendedLambda -> m ThunkRef
convertToThunks (ctx ::= e) = do thId <- ThunkRef <$> freshId'
                                 base <- convertBase e
                                 ctx' <- convertCtx ctx
                                 fv <- computeThunkFV' base ctx'
                                 let thunk = Thunk { thId = thId
                                                   , thExpr = base
                                                   , thCounter = 1
                                                   , thContext = ctx'
                                                   , thFree = fv
                                                   , thNormalized = False
                                                   }
                                 updThunks (HM.insert thId thunk)
                                 return thId

convertBase :: MonadState ThunkState m => ExtendedLambdaBase ExtendedLambda -> m (ExtendedLambdaBase ThunkRef)
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

computeThunkFV :: MonadState ThunkState m => Thunk -> m Thunk
computeThunkFV th = (\fv -> th { thFree = fv }) <$> computeThunkFV' (thExpr th) (thContext th)

computeThunkFV' :: MonadState ThunkState m => ExtendedLambdaBase ThunkRef -> ThunkContext -> m (HS.HashSet Var)
computeThunkFV' base ctx = do
    ctxFV <- ctxInnerFV ctx
    baseFV <- baseToFreeVars base
    return $ (ctxFV `HS.union` baseFV) `HS.difference` ctxVars
  where ctxVars = HS.fromList $ HM.keys ctx

thFree' thRef = thFree <$> getThunk thRef

baseToFreeVars :: MonadState ThunkState m => ExtendedLambdaBase ThunkRef -> m (HS.HashSet Var)
baseToFreeVars (l :~ r) = HS.union <$> thFree' l <*> thFree' r
baseToFreeVars (l :@ r) = HS.union <$> thFree' l <*> thFree' r
baseToFreeVars (Abs v e) = HS.delete v <$> thFree' e
baseToFreeVars (V v) = return $ HS.singleton v
baseToFreeVars _ = return HS.empty

convertCtx :: MonadState ThunkState m => ELContext -> m (HM.HashMap Var ThunkRef)
convertCtx ctx = HM.fromList <$> mapM (\(v, e) -> (,) v <$> convertToThunks e) (LHM.toList ctx)

