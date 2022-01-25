{-# LANGUAGE TupleSections #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts, FlexibleInstances, DeriveGeneric #-}

module Algebra.Morphism.Monoids where
import Algebra.Classes
import Prelude (Show,Eq,Ord,Monoid(..),Semigroup(..))
import GHC.Generics
import Data.Binary

newtype Sum a = Sum {fromSum :: a} deriving (Generic,Ord,Eq,Show)

instance Binary a => Binary (Sum a)

instance Additive a => Monoid (Sum a) where
  mempty = Sum zero
  mappend = (<>)

instance Additive a => Semigroup (Sum a) where
  (<>) (Sum x) (Sum y) = Sum (x + y)

newtype Product a = Product {fromProduct :: a} deriving (Generic,Ord,Eq,Show)

instance Multiplicative a => Semigroup (Product a) where
  (<>) (Product x) (Product y) = Product (x * y)

instance Multiplicative a => Monoid (Product a) where
  mempty = Product one
  mappend = (<>)
