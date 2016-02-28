{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
    MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module ExtendedLambda.Thunk.State where

import Control.Monad
import Control.Monad.State.Strict
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


updThunks :: MonadState ThunkState m => (HM.HashMap ThunkId (Thunk ThunkRef) -> HM.HashMap ThunkId (Thunk ThunkRef)) -> m ()
updThunks f = modify $ \st -> st { thunks = f $ thunks st }

instance Monad m => MonadThunkState ThunkRef (StateT ThunkState m) where
  getThunk (ThunkRef thId) = gets ((HM.! thId) . thunks)
  updThunk (ThunkRef thId) f = updThunks $ \ths -> HM.insert thId (f $ ths HM.! thId) ths
  addThunk th = updThunks (HM.insert (thId th) th) >> return (ThunkRef $ thId th)

instance Monad m => MonadThunkId (StateT ThunkState m) where
  nextThunkId = freshId'

data ThunkState = ThunkState { thunks :: HM.HashMap ThunkId (Thunk ThunkRef)
                             , idCounter :: Int
                             }

newtype ThunkRef = ThunkRef Int
  deriving (Eq, Hashable)

instance Show ThunkRef where
  show (ThunkRef i) = '#' : show i

instance CounterBasedState ThunkState where
  counterNext s = let i = idCounter s in (i, s { idCounter = i + 1 })
  counterEmptyState = initState

initState = ThunkState { thunks = HM.empty
                       , idCounter = 0
                       }
