{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving, Rank2Types #-}
module ExtendedLambda.Thunk.ST where

import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Control.Monad.ST.Trans
import Control.Monad.Trans.Class
import Control.Monad.Error.Class (catchError)
import Control.Monad.Trans.Either (left, EitherT)
import Control.Monad.Trans.Except (throwE)
import Data.List
import Debug.Trace
import Common
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS
import qualified Data.LinkedHashMap.IntMap as LHM
import Data.Hashable
import ExtendedLambda.Types
import ExtendedLambda.Base
import ExtendedLambda.Thunk.Base

data ThunkRef s = ThunkRef { trRef :: STRef s (Thunk (ThunkRef s))
                           , trId :: Int
                           }

instance Eq (ThunkRef s) where
  a == b = trId a == trId b

instance Show (ThunkRef s) where
  show x = "#" ++ show (trId x)

type ThunkSTT s m = ReaderT (STRef s Int) (STT s m)

instance Monad m => MonadThunkId (ThunkSTT s m) where
  nextThunkId = ask >>= \r -> lift (readSTRef r) >>= \c -> lift (writeSTRef r (c + 1)) >> return c

instance Monad m => MonadThunkState (ThunkRef s) (ThunkSTT s m) where
  updThunk ref@(ThunkRef r _) f = trace' ("updThunk " ++ show ref) $ lift $ readSTRef r >>= writeSTRef r . f
  addThunk th = lift $ flip ThunkRef (thId th) <$> newSTRef th
  getThunk (ThunkRef r _) = lift $ readSTRef r

evalThunkSTT :: Monad m => (forall s. ThunkSTT s m a) -> m a
evalThunkSTT m = runST $ runReaderT m =<< newSTRef 0


