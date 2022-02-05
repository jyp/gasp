{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts, FlexibleInstances, DeriveGeneric #-}

module Algebra.Morphism.Exponential where

import Prelude (Show,Eq,Ord,Integer,Functor,Foldable)
import Data.Traversable
import Algebra.Classes

newtype Exp a = Exp a deriving (Show,Eq,Ord,Foldable,Traversable,Functor)

fromExp :: Exp a -> a
fromExp (Exp x) = x

instance Additive a => Multiplicative (Exp a) where
  Exp a * Exp b = Exp (a + b)
  one = Exp zero
  Exp a ^+ n = Exp (times n a)

instance Group a => Division (Exp a) where
  recip (Exp a) = Exp (negate a)
  Exp a / Exp b = Exp (a - b)

instance Field a => Roots (Exp a) where
  root n (Exp x) = Exp (x / fromInteger n)


newtype Log a = Log a deriving (Show,Eq,Ord)

fromLog :: Log a -> a
fromLog (Log x) = x

instance Multiplicative a => Additive (Log a) where
  Log a + Log b = Log (a * b)
  zero = Log one
  times n (Log a) = Log (a ^+ n)

instance Multiplicative a => Scalable Integer (Log a) where
  n *^ Log x = Log (x ^+ n)
  
instance Division a => Group (Log a) where
  negate (Log a) = Log (recip a)
  Log a - Log b = Log (a / b)

-- instance Roots a => Field (Log a) where
-- fromRational x = Log (root (denominator x) (fromInteger (numerator x)))

