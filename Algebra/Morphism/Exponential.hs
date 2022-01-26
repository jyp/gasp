{-# LANGUAGE TupleSections #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts, FlexibleInstances, DeriveGeneric #-}

module Algebra.Morphism.Exponential where

import Prelude (Show,Eq,Ord,Integer)
import Algebra.Classes

newtype Exponential a = Exponential {fromExponential :: a} deriving (Show,Eq,Ord)

instance Additive a => Multiplicative (Exponential a) where
  Exponential a * Exponential b = Exponential (a + b)
  one = Exponential zero
  Exponential a ^+ n = Exponential (times n a)

instance Group a => Division (Exponential a) where
  recip (Exponential a) = Exponential (negate a)
  Exponential a / Exponential b = Exponential (a - b)

instance Field a => Roots (Exponential a) where
  root n (Exponential x) = Exponential (x / fromInteger n)


newtype Logarithm a = Logarithm {fromLogarithm :: a} deriving (Show,Eq,Ord)

instance Multiplicative a => Additive (Logarithm a) where
  Logarithm a + Logarithm b = Logarithm (a * b)
  zero = Logarithm one
  times n (Logarithm a) = Logarithm (a ^+ n)

instance Multiplicative a => Scalable Integer (Logarithm a) where
  n *^ Logarithm x = Logarithm (x ^+ n)
  
instance Division a => Group (Logarithm a) where
  negate (Logarithm a) = Logarithm (recip a)
  Logarithm a - Logarithm b = Logarithm (a / b)

-- instance Roots a => Field (Logarithm a) where
-- fromRational x = Logarithm (root (denominator x) (fromInteger (numerator x)))

