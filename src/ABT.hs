{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module ABT where

import qualified Data.Set as Set
import Data.Type.Equality (TestEquality (..), (:~:) (Refl))
import Var (Var (FreeVar), VarM, metaVar)

data Sort
  = I
  | Sort :=> Sort

data Term s a where
  Var :: Var s a -> Term s a
  Abs :: Typeable a => Var s a -> Term s b -> Term s (a ':=> b)
  App :: Term s (a ':=> b) -> Term s a -> Term s b

data Exists f = forall a. Exists (f a)
  deriving (Eq, Ord)

metaVars :: Term s a -> Set.Set (Exists (Var s))
metaVars (Var FreeVar {}) = Set.empty
metaVars (Var x) = Set.singleton x

rename :: Var s (a :: Sort) -> Var s a -> Term s b -> Term s b
rename x y (Var z) =
  case testEquality x z of
    Just Refl -> Var y
    Nothing -> Var z
rename x y (Abs z t) =
  case testEquality x z of
    Just _ -> Abs z t
    Nothing -> Abs z (rename x y t)
rename x y (App t1 t2) = App (rename x y t1) (rename x y t2)

subst :: Var s a -> Term s a -> Term s b -> VarM s (Term s b)
subst x t' (Var z) =
  case testEquality x z of
    Just Refl -> return t'
    Nothing -> return (Var z)
subst x t' (Abs z t) = do
  z' <- metaVar
  Abs z' <$> subst x t' (rename z z' t)
subst x t' (App t1 t2) = App <$> subst x t' t1 <*> subst x t' t2

reduce :: Term s a -> VarM s (Term s a)
reduce (Var x) = return (Var x)
reduce (Abs x t) = Abs x <$> reduce t
reduce (App (Abs x t1) t2) = subst x t2 t1 >>= reduce
reduce (App t1 t2) = App <$> reduce t1 <*> reduce t2

simplify :: (Term s a, Term s a) -> m (Set Constraint)
simplify (t1, t2)
  | t1 == t2 && null (metaVars t1) = return Set.empty
  | reduce t1 /= t1 = simplify (reduce t1, t2)
  | reduce t2 /= t2 = simplify (t1, reduce t2)
simplify _ = error "Help!"