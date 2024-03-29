{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Algebra.Category.Op where

import Algebra.Category
import Algebra.Classes
import Algebra.Category.Objects
import Prelude (Show)
import Test.QuickCheck

newtype Op k a b = Op {fromOp :: k b a}

deriving instance Additive (f b a) => Additive (Op f a b)
deriving instance Group (f b a) => Group (Op f a b)
deriving instance Arbitrary (f b a) => Arbitrary (Op f a b)
deriving instance Show (f b a) => Show (Op f a b)
deriving instance TestEqual (f b a) => TestEqual (Op f a b)

instance Category k => Category (Op k) where
  type Obj (Op k) = Obj k
  id = Op id
  Op f . Op g = Op (g . f)

instance Monoidal x i k => Monoidal x i (Op k) where
  Op f ⊗ Op g = Op (f ⊗ g)
  assoc = Op assoc_
  assoc_ = Op assoc
  unitorR = Op unitorR_
  unitorR_ = Op unitorR
  unitorL = Op unitorL_
  unitorL_ = Op unitorL

instance Cartesian x i k => CoCartesian x i (Op k) where
  inl = Op exl
  inr = Op exr
  new = Op dis
  jam = Op dup
  Op f ▿ Op g = Op (f ▵ g)

instance CoCartesian x i k => Cartesian x i (Op k) where
  exl = Op inl
  exr = Op inr
  dis = Op new
  dup = Op jam
  Op f ▵ Op g = Op (f ▿ g)

instance Braided x i k => Braided x i (Op k) where
  swap = Op swap
  swap_ = Op swap_

instance Symmetric x i k => Symmetric x i (Op k) where

instance (con ~ Obj k, Con' x con, UnCon r con, UnCon l con, con i, Autonomous x i r l k, Braided x i k) => Autonomous x i l r (Op k) where
  turn = swap . Op turn'
  turn' = Op turn . swap

instance (con ~ Obj k, Con' x con, UnCon d con, con i, Compact x i d k, Braided x i k) => Compact x i d (Op k) where


