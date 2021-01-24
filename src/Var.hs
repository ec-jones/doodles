{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Var
  ( Var (FreeVar, name),
    VarM,
    runVarM,
    metaVar,
  )
where

import Control.Monad.ST (ST, runST)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import Data.Type.Equality (TestEquality (..), (:~:))
import Data.Typeable (cast, (:~:) (Refl))

data Var s (a :: k)
  = (Typeable a, Typeable k) =>
    FreeVar
      { name :: !Text
      }
  | (Typeable a, Typeable k) =>
    MetaVar
      { name :: !Text,
        uniq :: {-# UNPACK #-} !Int
      }

instance TestEquality (Var s) where
  testEquality :: forall a b. Var s a -> Var s b -> Maybe (a :~: b)
  testEquality (FreeVar x) (FreeVar y)
    | x == y = cast (Refl @a)
  testEquality (MetaVar _ x) (MetaVar _ y)
    | x == y = cast (Refl @a)
  testEquality _ _ = Nothing

newtype VarM s a = VarM
  { unIdM :: STRef s Int -> ST s a
  }

instance Functor (VarM s) where
  fmap f (VarM u) = VarM (fmap (fmap f) u)

instance Applicative (VarM s) where
  pure x = VarM (\_ -> pure x)

  VarM f <*> VarM x = VarM (\ref -> f ref <*> x ref)

instance Monad (VarM s) where
  return x = VarM (\_ -> return x)

  VarM x >>= f =
    VarM
      ( \ref -> do
          VarM k <- f <$> x ref
          k ref
      )

runVarM :: (forall s. VarM s a) -> a
runVarM f = runST (newSTRef 0 >>= unIdM f)

metaVar :: (Typeable (a :: k), Typeable k) => VarM s (Var s a)
metaVar = VarM $ \ref -> do
  n <- readSTRef ref
  writeSTRef ref (n + 1)
  return
    MetaVar
      { name = "META " <> show n,
        uniq = n
      }