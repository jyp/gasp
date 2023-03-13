{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Algebra.Types where

import Data.Kind
import Data.Constraint (Dict(..))

class AlgebraicKind k where
  data (a::k) ⊕ (b::k) :: k
  data (a::k) ⊗ (b::k) :: k
  data Dual (a::k) :: k
  data One :: k
  data Zero :: k


instance AlgebraicKind Type where
  data x ⊕ y = Inj1 x | Inj2 y deriving (Eq,Ord,Show)
  data x ⊗ y = Pair {π1 :: x, π2 :: y} deriving (Eq,Ord,Show)
  data Dual x = DualType x deriving (Eq,Ord,Show)
  data One = Unit deriving (Eq,Ord,Enum,Bounded,Show)
  data Zero deriving (Eq,Ord,Show)



inhabitants :: Finite a => [a]
inhabitants = [minBound..maxBound]

class (Enum a, Bounded a, Eq a, Ord a) => Finite a where
  typeSize :: Int
  typeSize = fromEnum (maxBound @a) - fromEnum (minBound @a) + 1
  finiteFstsnd :: forall α b. (a ~ (α⊗b)) => Dict (Finite α, Finite b)
  finiteFstsnd = error "finiteFstsnd: not a product type"
  finiteLeftRight :: forall α b. (a ~ (α⊕b)) => Dict (Finite α, Finite b)
  finiteLeftRight = error "finiteFstsnd: not a sum type"


fromZero :: forall a. Finite a => Int -> a
fromZero i = toEnum (i + fromEnum (minBound @a))

instance (Bounded x, Bounded y) => Bounded (x⊕y) where
  minBound = Inj1 minBound
  maxBound = Inj2 maxBound

instance (Finite x, Finite y) => Enum (x⊕y) where
  toEnum i = if i < typeSize @x then Inj1 (toEnum i) else Inj2 (toEnum (i-typeSize @x))
  fromEnum = \case
     Inj1 x -> fromEnum x
     Inj2 x -> fromEnum x + typeSize @x

instance (Finite x, Finite y) => Finite (x⊕y) where
  finiteLeftRight = Dict
instance (Finite x, Finite y) => Enum (x⊗y) where
  toEnum k = Pair (toEnum i) (toEnum j)
    where (j,i) = k `divMod` typeSize @x
  fromEnum (Pair x y) = fromEnum x + fromEnum y * (typeSize @x)
instance (Finite x, Finite y) => Finite (x⊗y) where
  finiteFstsnd = Dict
instance Finite Bool
instance Finite One

instance (Bounded x, Bounded y) => Bounded (x⊗y) where
  minBound = minBound `Pair` minBound
  maxBound = maxBound `Pair` maxBound

  
instance Enum Zero where
  toEnum = error "toEnum: Zero"
  fromEnum = \case
instance Bounded Zero where
  minBound = error "minBound: Zero"
  maxBound = error "maxBound: Zero"
instance Finite Zero where
  typeSize = 0

-- | Algebraic structure for (Type -> Type) is in the exponential
-- level Finitecause functor composition is generally where the action is.
instance AlgebraicKind (Type -> Type) where
  data (f ⊗ g) x = Comp {fromComp :: (f (g x))} deriving (Foldable, Traversable, Functor)
  data (f ⊕ g) x = FunctorProd (f x) (g x) deriving (Foldable, Traversable, Functor)
  data One x = FunctorUnit x deriving (Foldable, Traversable, Functor)
  data Dual f x = FunctorDual {fromFunctorDual :: f x} deriving (Foldable, Traversable, Functor)
  data Zero x = FunctorZero deriving (Foldable, Traversable, Functor)

instance Applicative One where
  pure = FunctorUnit
  FunctorUnit f <*> FunctorUnit x = FunctorUnit (f x)
  
instance Applicative Zero where
  pure _ = FunctorZero
  _ <*> _ = FunctorZero

instance (Applicative f, Applicative g) => Applicative (f ⊗ g) where
  Comp f <*> Comp x = Comp ((fmap (<*>) f) <*> x)
  pure x = Comp (pure (pure x))

instance (Applicative f, Applicative g) => Applicative (f ⊕ g) where
  FunctorProd f g <*> FunctorProd x y = FunctorProd (f <*> x) (g <*> y)
  pure x = FunctorProd (pure x) (pure x)

instance (Applicative f) => Applicative (Dual f) where
  FunctorDual f <*> FunctorDual x = FunctorDual (f <*> x)
  pure x = FunctorDual (pure x)

