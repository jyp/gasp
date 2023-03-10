{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Algebra.Types where

import Data.Kind

class AlgebraicKind k where
  data (a::k) ⊕ (b::k) :: k
  data (a::k) ⊗ (b::k) :: k
  data Dual (a::k) :: k
  data One :: k
  data Zero :: k


instance AlgebraicKind Type where
  data x ⊕ y = Inj1 x | Inj2 y deriving (Eq,Ord)
  data x ⊗ y = Pair {π1 :: x, π2 :: y} deriving (Eq,Ord)
  data Dual x = DualType x deriving (Eq,Ord)
  data One = One deriving (Eq,Ord)
  data Zero deriving (Eq,Ord)


-- | Algebraic structure for (Type -> Type) is in the exponential
-- level because functor composition is generally where the action is.
instance AlgebraicKind (Type -> Type) where
  data (f ⊗ g) x = Comp {fromComp :: (f (g x))} deriving (Foldable, Traversable, Functor)
  data (f ⊕ g) x = FunctorProd (f x) (g x) deriving (Foldable, Traversable, Functor)
  data One x = FunctorOne x deriving (Foldable, Traversable, Functor)
  data Dual f x = FunctorDual {fromFunctorDual :: f x} deriving (Foldable, Traversable, Functor)
  data Zero x = Const {fromConst :: x} deriving (Foldable, Traversable, Functor)


instance (Applicative f, Applicative g) => Applicative (f ⊗ g) where
  Comp f <*> Comp x = Comp ((fmap (<*>) f) <*> x)
  pure x = Comp (pure (pure x))

instance (Applicative f, Applicative g) => Applicative (f ⊕ g) where
  FunctorProd f g <*> FunctorProd x y = FunctorProd (f <*> x) (g <*> y)
  pure x = FunctorProd (pure x) (pure x)

instance (Applicative f) => Applicative (Dual f) where
  FunctorDual f <*> FunctorDual x = FunctorDual (f <*> x)
  pure x = FunctorDual (pure x)

