{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
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
import Data.Functor.Rep
import Data.Distributive
import GHC.Generics hiding (Rep)
import Test.QuickCheck hiding (tabulate,collect)

class SumKind k where
  data (a::k) ⊕ (b::k) :: k
  data Zero :: k

class ProdKind k where
  data (a::k) ⊗ (b::k) :: k
  data One :: k

class DualKind k where
  data Dual (a::k) :: k

data Repr :: k -> Type where
  RPlus :: Repr a -> Repr b -> Repr (a ⊕ b)
  RTimes :: Repr a -> Repr b -> Repr (a ⊗ b)
  ROne :: Repr One
  RZero :: Repr Zero

instance SumKind Type where
  data x ⊕ y = Inj1 x | Inj2 y deriving (Eq,Ord,Show,Generic)
  data Zero deriving (Eq,Ord,Show)

instance ProdKind Type where
  data x ⊗ y = Pair {π1 :: x, π2 :: y} deriving (Eq,Ord,Show,Generic)
  data One = Unit deriving (Eq,Ord,Enum,Bounded,Show)

instance DualKind Type where
  data Dual x = DualType x deriving (Eq,Ord,Show,Generic)


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

instance CoArbitrary One where
  coarbitrary _ = id
instance CoArbitrary Zero where
  coarbitrary _ = id
instance (CoArbitrary f, CoArbitrary g) => CoArbitrary (f ⊕ g) where
instance (CoArbitrary f, CoArbitrary g) => CoArbitrary (f ⊗ g) where


-- | Algebraic structure for (Type -> Type) is in the exponential
-- level because functor composition is generally where the action is.
instance SumKind (Type -> Type) where
  data (f ⊕ g) x = FunctorProd {prodFst :: f x, prodSnd :: g x} deriving (Foldable, Traversable, Functor,Generic1,Eq)
  data Zero x = FunctorZero deriving (Foldable, Traversable, Functor, Generic1, Eq)
  
instance ProdKind (Type -> Type) where
  data (f ⊗ g) x = Comp {fromComp :: (f (g x))} deriving (Foldable, Traversable, Functor, Generic1, Eq)
  data One x = FunctorUnit {fromFunctorUnit :: x} deriving (Foldable, Traversable, Functor, Generic1, Eq)

instance DualKind (Type -> Type) where
  data Dual f x = FunctorDual {fromFunctorDual :: f x} deriving (Foldable, Traversable, Functor, Generic1, Show, Eq)

deriving instance Show (Zero (x :: Type))
deriving instance Show x => Show (One (x :: Type))
deriving instance (Show (a x), Show (b x)) => Show ((a⊕b) (x :: Type))
deriving instance (Show (a (b x))) => Show ((a⊗b) (x :: Type))

data Ring1Closed con = Ring1Closed {
  zero1Closed :: forall (x :: Type). Dict (con (Zero x)),
  one1Closed :: forall (x :: Type). con x => Dict (con (One x)),
  plus1Closed :: forall a b (x :: Type). (con (a x), con (b x)) => Dict (con ((a⊕b) x)),
  times1Closed :: forall a b (x :: Type). (con (a (b x))) => Dict (con ((a⊗b) x))
                          }

showRing1Closed :: Ring1Closed Show
showRing1Closed = Ring1Closed Dict Dict Dict Dict

instance Distributive Zero where
  distribute _ = FunctorZero
instance Distributive One where
  distribute = FunctorUnit . fmap fromFunctorUnit
instance Representable Zero where
  type Rep Zero = Zero
  index FunctorZero = \case
  tabulate _ = FunctorZero
instance Representable One where
  type Rep One = One
  index (FunctorUnit x) _ = x
  tabulate f = FunctorUnit (f Unit)
instance (Distributive v, Distributive w) => Distributive (v ⊗ w) where
  distribute = Comp . fmap distribute . distribute . fmap fromComp
instance (Representable v, Representable w) => Representable (v ⊗ w) where
  type Rep (v ⊗ w) = Rep v ⊗ Rep w
  index (Comp f) (i `Pair` j) = (f `index` i) `index` j
  tabulate f = Comp (tabulate (\i -> tabulate (\j -> f (i `Pair` j))))
instance (Distributive v, Distributive w) => Distributive (v ⊕ w) where
  collect f x = FunctorProd (collect (prodFst . f) x) (collect (prodSnd . f) x)
instance (Representable v, Representable w) => Representable (v ⊕ w) where
  type Rep (v ⊕ w) = Rep v ⊕ Rep w
  index (FunctorProd x y) = \case
    Inj1 i -> index x i
    Inj2 i -> index y i
  tabulate f = FunctorProd (tabulate (f . Inj1)) (tabulate (f . Inj2))

instance Arbitrary1 One where
  liftArbitrary = fmap FunctorUnit
instance Arbitrary1 Zero where
  liftArbitrary _ = pure FunctorZero
instance (Arbitrary1 f, Arbitrary1 g) => Arbitrary1 (f ⊕ g) where
  liftArbitrary g = FunctorProd <$> liftArbitrary g <*> liftArbitrary g
instance (Arbitrary1 f, Arbitrary1 g) => Arbitrary1 (f ⊗ g) where
  liftArbitrary g = Comp <$> liftArbitrary (liftArbitrary g)

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

