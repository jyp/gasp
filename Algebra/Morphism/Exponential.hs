{-# LANGUAGE TupleSections #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts, FlexibleInstances, DeriveGeneric #-}

module Algebra.Morphism.Exponential where

import Prelude (Show,Eq,Ord)

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

