{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}

module Unify where

import Control.Monad (when, (>=>))
import qualified Data.Map as Map
import Term (Herbrand (zipTerms, (↯)), Term (Term, Var), Theta, subst, vars)

-- Unification effect that updates substitutions
data Unifier sig a k
  = Elim a (Term sig a) (Unifier sig a k)
  | Fresh (a -> Unifier sig a k)
  | Result (UnificationResult sig a k)
  deriving (Functor)

data UnificationResult sig a k
  = Occurs a (Term sig a)
  | Conflict (Term sig a) (Term sig a)
  | Success k
  deriving (Show, Functor)

elim :: a -> Term sig a -> Unifier sig a ()
elim a t = Elim a t (Result (Success ()))

fresh :: Unifier sig a a
fresh = Fresh (Result . Success)

occurs :: a -> Term sig a -> Unifier sig a k
occurs a t = Result (Occurs a t)

conflict :: Term sig a -> Term sig a -> Unifier sig a k
conflict a t = Result (Conflict a t)

instance Applicative (Unifier sig a) where
  pure = Result . Success

  Elim a t k <*> u = Elim a t (k <*> u)
  Fresh k <*> u = Fresh (\a -> k a <*> u)
  Result (Occurs a t) <*> _ = Result (Occurs a t)
  Result (Conflict s t) <*> _ = Result (Conflict s t)
  Result (Success f) <*> u = fmap f u

instance Monad (Unifier sig a) where
  return = Result . Success

  Elim x t k >>= f = Elim x t (k >>= f)
  Fresh k >>= f = Fresh (k >=> f)
  Result (Occurs a t) >>= _ = Result (Occurs a t)
  Result (Conflict s t) >>= _ = Result (Conflict s t)
  Result (Success res) >>= f = f res

-- The unify effect handler
runUnifier :: (Functor sig, Ord a) => [a] -> Unifier sig a k -> UnificationResult sig a (Theta sig a, k)
runUnifier as (Elim a t k) =
  case runUnifier as k of
    Success (theta, res) -> Success (subst (Map.singleton a t) <$> theta, res)
    err -> err
runUnifier _ (Result res) = fmap (Map.empty,) res
runUnifier (a : as) (Fresh k) = runUnifier as (k a)
runUnifier [] (Fresh _) = error "Insufficient fresh variables!"

unify :: (Herbrand sig, Ord a) => Term sig a -> Term sig a -> Unifier sig a (Term sig a)
unify t@(Term f) s@(Term g) = do
  when (f ↯ g) $ conflict t s
  Term <$> zipTerms unify f g
unify t@(Var a) s@(Var b) = do
  when (a /= b) $ conflict t s
  return t
unify s (Var a) = do
  when (a `elem` vars s) $ occurs a s
  elim a s
  return (Var a)
unify (Var a) s = do
  when (a `elem` vars s) $ occurs a s
  elim a s
  return (Var a)

antiUnify :: (Herbrand sig, Ord a) => Term sig a -> Term sig a -> Unifier sig a (Term sig a)
antiUnify (Term f) (Term g) =
  if f ↯ g
    then Var <$> fresh
    else Term <$> zipTerms antiUnify f g
antiUnify (Var a) (Var b) =
  if a /= b
    then Var <$> fresh
    else return (Var a)
antiUnify s (Var a) = do
  when (a `elem` vars s) $ occurs a s
  return (Var a)
antiUnify (Var a) s = do
  when (a `elem` vars s) $ occurs a s
  return (Var a)