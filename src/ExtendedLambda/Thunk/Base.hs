{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module ExtendedLambda.Thunk.Base where

import Control.Monad.Error.Class (catchError)
import Control.Monad.Trans.Either (left, EitherT)
import Control.Monad.Trans.Except (throwE)
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
traceM' = const $ return ()
trace' x y = y
--traceM' = (=<<) traceM
--trace' = trace

newtype ThunkRef = ThunkRef Int
  deriving (Eq, Hashable)

instance Show ThunkRef where
  show (ThunkRef i) = '#' : show i

type ThunkContext = HM.HashMap Var ThunkRef

type ThunkId = Int

data Thunk = Thunk { thId :: ThunkId
                   , thExpr :: ExtendedLambdaBase ThunkRef
                   , thCounter :: Int
                   , thContext :: ThunkContext
                   , thFree :: HS.HashSet Var
                   , thNormalized :: Maybe ThunkRef
                   }

data ThunkState = ThunkState { thunks :: HM.HashMap ThunkId Thunk
                             , idCounter :: Int
                             , ifTrueTh :: ThunkRef
                             , ifFalseTh :: ThunkRef
                             , caseL :: ThunkRef
                             , caseR :: ThunkRef
                             }


class Monad m => MonadThunkState s ref m | m -> s, m -> ref where
  updThunk :: ref -> (Thunk -> Thunk) -> m ()
  addThunk :: Thunk -> m ref
  getThunk :: ref -> m Thunk
  nextThunkId :: m ThunkId

updThunks :: MonadState ThunkState m => (HM.HashMap ThunkId Thunk -> HM.HashMap ThunkId Thunk) -> m ()
updThunks f = modify $ \st -> st { thunks = f $ thunks st }

instance MonadState ThunkState m => MonadThunkState ThunkState ThunkRef m where
  getThunk (ThunkRef thId) = gets ((HM.! thId) . thunks)
  updThunk (ThunkRef thId) f = updThunks $ \ths -> HM.insert thId (f $ ths HM.! thId) ths
  addThunk th = updThunks (HM.insert (thId th) th) >> return (ThunkRef $ thId th)
  nextThunkId = freshId'

newThunk :: MonadThunkState ThunkState ThunkRef m => Thunk -> m ThunkRef
newThunk th = do thId <- nextThunkId
                 th' <- computeThunkFV th
                 addThunk th' { thId = thId, thCounter = 1, thNormalized = Nothing }

initState = execState initiateThunkState $ ThunkState { thunks = HM.empty
                       , idCounter = 0
                       , ifTrueTh = undefined
                       , ifFalseTh = undefined
                       , caseL = undefined
                       , caseR = undefined
                       }

thNormalized' :: MonadThunkState ThunkState ThunkRef m => ThunkRef -> m (Maybe ThunkRef)
thNormalized' = fmap thNormalized . getThunk

-- set thRef' as normalized for thRef, returns thRef'
setThNormalized :: MonadThunkState ThunkState ThunkRef m => ThunkRef -> ThunkRef -> m ThunkRef
setThNormalized thRef thRef' = do
     updThunk thRef (\s -> s { thNormalized = Just thRef' })
     traceM' $ (++) ("-- " ++ show thRef ++ " normalized to ") <$> thShowIdent 0 thRef'
     return thRef'

getCached :: MonadThunkState ThunkState ThunkRef m => ThunkRef -> m ThunkRef
getCached thRef = maybe thRef id <$> thNormalized' thRef

withCache :: MonadState ThunkState n => (ThunkRef -> EitherT ThunkRef n ThunkRef) -> ThunkRef -> EitherT ThunkRef n ThunkRef
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



instance CounterBasedState ThunkState where
  counterNext s = let i = idCounter s in (i, s { idCounter = i + 1 })
  counterEmptyState = initState

ctxInnerFV :: MonadThunkState ThunkState ThunkRef m => ThunkContext -> m (HS.HashSet Var)
ctxInnerFV = foldM (\b a -> HS.union b <$> thFree' a) HS.empty . HM.elems

encloseCtx :: MonadThunkState ThunkState ThunkRef m => ThunkRef -> m ()
encloseCtx thRef = do
      th <- getThunk thRef
      baseFV <- baseToFreeVars $ thExpr th
      let ctx = thContext th
      ctx' <- traverse (joinCtx ctx) ctx
      let ctx'' = HM.intersectionWith (const id) (HS.toMap baseFV) ctx'
      updThunk thRef (\s -> s { thContext = ctx'' })

-- thRef's ctx entries are assummed to be enclosed
propagateCtx :: MonadThunkState ThunkState ThunkRef m => ThunkRef -> m ()
propagateCtx thRef = do
  th <- getThunk thRef
  base' <- propagateCtxToBase (thContext th) (thExpr th)
  case base' of
    Just e -> updThunk thRef (\s -> s { thExpr = e, thContext = HM.empty })
    _ -> return ()

joinCtx :: MonadThunkState ThunkState ThunkRef m => ThunkContext -> ThunkRef -> m ThunkRef
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
            newThunk $ th { thContext = newCtx }

normalizeCtx :: MonadThunkState ThunkState ThunkRef m => HS.HashSet Var -> ThunkContext -> [(Var, ThunkRef)] -> m [(Var, ThunkRef)]
normalizeCtx _ rCtx [] = return []
normalizeCtx vs rCtx ((v, e) : as) = if v `HS.member` vs
                                        then normalizeCtx vs (HM.insert v e rCtx) as
                                        else (:) . (,) v <$> joinCtx rCtx e
                                                         <*> normalizeCtx (HS.insert v vs) rCtx as


joinCtxM :: MonadThunkState ThunkState ThunkRef m => ThunkContext -> ThunkContext -> m ThunkContext
joinCtxM m ctx = HM.union ctx <$> mapM (joinCtx m) (HM.difference m ctx)

thShowIdent' :: MonadThunkState ThunkState ThunkRef m => Int -> ExtendedLambdaBase ThunkRef -> m String
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
  where show' i r = do el <- thExpr <$> getThunk r
                       case el of
                         (_ :@ _) -> (\x -> "(" ++ x ++ ")") <$> thShowIdent i r
                         _ -> thShowIdent i r
thShowIdent' _ (V v) = return v

thShowIdent :: MonadThunkState ThunkState ThunkRef m => Int -> ThunkRef -> m String
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
showLBs :: MonadThunkState ThunkState ThunkRef m => Int -> ThunkContext -> m [String]
showLBs i = mapM (\(v, s) -> ((v ++ " = ") ++) <$> thShowIdent i s) . HM.toList

p i s = (replicate (i*2) ' ') ++ s
sps = flip replicate ' '

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

convertToThunks :: MonadState ThunkState m => ExtendedLambda -> m ThunkRef
convertToThunks (ctx ::= e) = do thId <- freshId'
                                 base <- convertBase e
                                 ctx' <- convertCtx ctx
                                 fv <- computeThunkFV' base ctx'
                                 let thunk = Thunk { thId = thId
                                                   , thExpr = base
                                                   , thCounter = 1
                                                   , thContext = ctx'
                                                   , thFree = fv
                                                   , thNormalized = Nothing
                                                   }
                                 addThunk thunk

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

computeThunkFV :: MonadThunkState ThunkState ThunkRef m => Thunk -> m Thunk
computeThunkFV th = (\fv -> th { thFree = fv }) <$> computeThunkFV' (thExpr th) (thContext th)

computeThunkFV' :: MonadThunkState ThunkState ThunkRef m => ExtendedLambdaBase ThunkRef -> ThunkContext -> m (HS.HashSet Var)
computeThunkFV' base ctx = do
    ctxFV <- ctxInnerFV ctx
    baseFV <- baseToFreeVars base
    return $ (ctxFV `HS.union` baseFV) `HS.difference` ctxVars
  where ctxVars = HS.fromList $ HM.keys ctx

propagateCached :: MonadThunkState ThunkState ThunkRef m => ThunkRef -> m ()
propagateCached thRef = thExpr <$> getThunk thRef >>= impl >>= \b -> updThunk thRef (\s -> s { thExpr = b })
  where
    impl (l :~ r) = impl2 l r (:~)
    impl (l :@ r) = impl2 l r (:@)
    impl (Abs v e) = Abs v <$> getCached e
    impl e = return e
    impl2 l r f = f <$> getCached l <*> getCached r

thFree' :: MonadThunkState ThunkState ThunkRef m => ThunkRef -> m (HS.HashSet Var)
thFree' thRef = thFree <$> getThunk thRef

-- ctx entries are assummed to be enclosed
propagateCtxToBase :: MonadThunkState ThunkState ThunkRef m => ThunkContext -> ExtendedLambdaBase ThunkRef -> m (Maybe (ExtendedLambdaBase ThunkRef))
propagateCtxToBase ctx (l :~ r)  = Just <$> ( (:~) <$> joinCtx ctx l <*> joinCtx ctx r )
propagateCtxToBase ctx (l :@ r)  = Just <$> ( (:@) <$> joinCtx ctx l <*> joinCtx ctx r )
propagateCtxToBase ctx (Abs v e) = Just <$> ( Abs v <$> joinCtx (HM.delete v ctx) e    )
propagateCtxToBase _ _ = return Nothing

baseToFreeVars :: MonadThunkState ThunkState ThunkRef m => ExtendedLambdaBase ThunkRef -> m (HS.HashSet Var)
baseToFreeVars (l :~ r) = HS.union <$> thFree' l <*> thFree' r
baseToFreeVars (l :@ r) = HS.union <$> thFree' l <*> thFree' r
baseToFreeVars (Abs v e) = HS.delete v <$> thFree' e
baseToFreeVars (V v) = return $ HS.singleton v
baseToFreeVars _ = return HS.empty

convertCtx :: MonadState ThunkState m => ELContext -> m (HM.HashMap Var ThunkRef)
convertCtx ctx = HM.fromList <$> mapM (\(v, e) -> (,) v <$> convertToThunks e) (LHM.toList ctx)

