{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}

module Flock where

import Control.Monad.Writer (First (First), MonadWriter (tell), runWriter, when)
import Data.Map qualified as Map
import Optics.Core (Lens', lens, over, set, view)

-- The class of vector spaces with an inner product
class (Monoid vec, Floating (Field vec)) => Vector vec where
  -- The vectors underlying field
  type Field vec

  -- The monoid structure is compatible scaling
  scale :: Field vec -> vec -> vec

  -- Positive definite bilinear operator with conjugate symmetry
  inner :: vec -> vec -> Field vec

-- Vectors form an additive group
delta :: Vector vec => vec -> vec -> vec
delta v1 v2 = v1 <> scale (-1) v2

norm :: Vector vec => Lens' vec (Field vec)
norm =
  lens
    (\v -> sqrt (inner v v))
    (\v s -> scale (s / sqrt (inner v v)) v)

newtype Flock vec a = Flock
  { getMap :: Map.Map vec a
  }

size :: Vector vec => Flock vec a -> Field vec
size (Flock m) = fromIntegral (Map.size m)

extract :: (Ord vec, Vector vec) => Flock vec a -> a
extract (Flock m) = m Map.! mempty

duplicate :: (Ord vec, Vector vec) => Flock vec a -> Flock vec (Flock vec a)
duplicate (Flock m) = Flock (Map.mapWithKey go m)
  where
    go v _ = Flock (Map.mapKeys (`delta` v) m)

-- A boid for some vector space
data Boid vec = Boid
  { vel :: vec,
    acc :: vec,
    maxSpeed :: Field vec,
    maxForce :: Field vec,
    desiredDist :: Field vec
  }

-- Reynolds formula for adjusting accelaration to an ideal velocity vector
seek :: Vector vec => Boid vec -> vec -> Boid vec
seek b centre =
  let steer = set norm (maxSpeed b) centre `delta` vel b
      force = set norm (maxForce b) steer
   in b {acc = acc b <> force}

-- Apply the accelaration to the velocity, and the velocity to the position
step :: (Ord vec, Vector vec) => Flock vec (Boid vec) -> Flock vec (Boid vec)
step (Flock m) =
  let (m', First (Just z)) = runWriter (Map.traverseWithKey go m)
   in Flock (Map.mapKeys (`delta` z) m') -- recentre flock
  where
    go pos b = do
      when (pos == mempty) $ tell (First (Just pos))
      return b {vel = vel b <> acc b}

cohesion :: (Ord vec, Vector vec) => Flock vec (Boid vec) -> Boid vec
cohesion flock =
  let boid = extract flock
      sum = Map.foldrWithKey (\v _ k -> v <> k) mempty (getMap flock)
      centre = scale (recip (size flock)) sum
   in seek boid centre -- as the boid is at (0, 0) the ideal velocity is the ideal location

align :: (Ord vec, Vector vec) => Flock vec (Boid vec) -> Boid vec
align flock =
  let boid = extract flock
      sum = Map.foldrWithKey (\_ b k -> vel b <> k) mempty (getMap flock)
      avg = scale (recip (size flock)) sum
   in seek boid avg

separate :: (Ord vec, Vector vec, Ord (Field vec)) => Flock vec (Boid vec) -> Boid vec
separate flock =
  let boid = extract flock
      sum =
        Map.foldrWithKey
          ( \v _ k ->
              if view norm v > desiredDist boid
                then over norm (\d -> recip (d * d)) v <> k -- Inverse square like repulsion
                else k
          )
          mempty
          (getMap flock)
      avg = scale (recip (size flock)) sum
   in seek boid avg