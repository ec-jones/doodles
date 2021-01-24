{-# LANGUAGE DeriveFunctor #-}

module Term
  ( Herbrand (..),
    Term (..),
    Theta,
    vars,
    subst,
  )
where

import Data.Functor.Classes (Show1 (liftShowList, liftShowsPrec), showsPrec1, showsUnaryWith)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Set as Set

-- Signatures that give rise to Herbrand-like structures
class (Functor sig, Foldable sig) => Herbrand sig where
  -- Check if the terms have conflicting, i.e. non-unifiable, shapes
  -- not (t ↯ t)
  (↯) :: sig a -> sig a -> Bool

  -- Combine two terms with an applicative action
  zipTerms :: Applicative f => (a -> a -> f a) -> sig a -> sig a -> f (sig a)

instance Herbrand [] where
  (↯) as bs = length as /= length bs

  zipTerms _ [] [] = pure []
  zipTerms f (a : as) (b : bs) = (:) <$> f a b <*> zipTerms f as bs
  zipTerms _ _ _ = error "Terms have conflicting shapes!"

instance Herbrand Maybe where
  (↯) as bs = isJust as /= isJust bs

  zipTerms _ Nothing Nothing = pure Nothing
  zipTerms f (Just x) (Just y) = Just <$> f x y
  zipTerms _ _ _ = error "Terms have a conflicting shape!"

instance Ord k => Herbrand (Map.Map k) where
  (↯) _ _ = False -- No maps are in conflict
  zipTerms f = Map.mergeA Map.preserveMissing Map.preserveMissing (Map.zipWithAMatched (const f))

-- Generic terms constructed from signature f with variables a
data Term sig a
  = Var a
  | Term (sig (Term sig a))
  deriving (Functor)

instance Show1 sig => Show1 (Term sig) where
  liftShowsPrec sp sl = go
    where
      go d (Var a) = showsUnaryWith sp "Var" d a
      go d (Term fa) = showsUnaryWith (liftShowsPrec go (liftShowList sp sl)) "Term" d fa

instance (Show1 sig, Show a) => Show (Term sig a) where
  showsPrec = showsPrec1

-- A collection of mutually coherent substitutions
type Theta sig a = Map.Map a (Term sig a)

-- The set of variables appearing in a term
vars :: (Foldable sig, Ord a) => Term sig a -> Set.Set a
vars (Var a) = Set.singleton a
vars (Term t) = foldMap vars t

-- Substitute a term for a variable in another term
subst :: (Functor sig, Ord a) => Theta sig a -> Term sig a -> Term sig a
subst theta t@(Var a) = fromMaybe t (Map.lookup a theta)
subst theta (Term t) = Term (fmap (subst theta) t)