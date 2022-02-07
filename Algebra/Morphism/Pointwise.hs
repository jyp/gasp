{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algebra.Morphism.Pointwise where

import Prelude (Functor(..), (.))
import Control.Applicative
import Algebra.Classes

-- | Function type where all functions are run pointwise.
newtype Pointwise x a = Pointwise (x -> a) deriving (Functor, Additive, Group, AbelianAdditive, Applicative)

fromPointwise :: Pointwise x a -> x -> a
fromPointwise (Pointwise x) = x

instance Multiplicative a => Multiplicative (Pointwise x a) where
  one  = pure one
  (*) = liftA2 (*)

instance Division a => Division (Pointwise x a) where
  recip  = fmap recip
  (/) = liftA2 (/)

instance Roots a => Roots (Pointwise x a) where
  root n  = fmap (root n)

instance Transcendental a => Transcendental (Pointwise x a) where
  pi = pure pi
  log = fmap log
  sin = fmap sin
  cos = fmap cos
  asin = fmap asin
  acos = fmap acos
  atan = fmap atan
  sinh = fmap sinh
  cosh = fmap cosh
  asinh = fmap asinh
  acosh = fmap acosh
  atanh = fmap atanh
  exp = fmap exp

instance Multiplicative a => Scalable (Pointwise x a) (Pointwise x a) where
  (*^) = (*)

instance Ring a => Ring (Pointwise x a) where
  fromInteger = pure . fromInteger

instance Field a => Field (Pointwise x a) where
  fromRational = pure . fromRational

