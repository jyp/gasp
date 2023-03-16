{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
module Algebra.Category.Op where

import Algebra.Category
import Prelude ()
newtype Op k a b = Op {fromOp :: k b a}

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

instance Symmetric x i k => Symmetric x i (Op k) where
