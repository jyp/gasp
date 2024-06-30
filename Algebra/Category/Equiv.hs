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
module Algebra.Category.Equiv where

import Algebra.Category
-- import Algebra.Classes
import Algebra.Category.Objects
import Prelude (Show)
-- import Test.QuickCheck

-- | Equivalence of a and b under category k (bi-directional morphisms; pair of k and Op k)
data Equiv k a b = Equiv {equivFwd :: k a b, equivBwd :: k b a}

-- deriving instance Additive (f b a) => Additive (Equiv f a b)
-- deriving instance Group (f b a) => Group (Equiv f a b)
-- deriving instance Arbitrary (f b a) => Arbitrary (Equiv f a b)
deriving instance (Show (f b a), Show (f a b)) => Show (Equiv f a b)
-- deriving instance TestEqual (f b a) => TestEqual (Equiv f a b)

instance Category k => Category (Equiv k) where
  type Obj (Equiv k) = Obj k
  id = Equiv id id
  Equiv f f' . Equiv g g' = Equiv (f . g) (g' . f')

instance Monoidal x i k => Monoidal x i (Equiv k) where
  Equiv f f' ⊗ Equiv g g' = Equiv (f ⊗ g) (f' ⊗ g')
  assoc = Equiv assoc assoc_
  assoc_ = Equiv assoc_ assoc
  unitorR = Equiv unitorR unitorR_
  unitorR_ = Equiv unitorR_ unitorR
  unitorL = Equiv unitorL unitorL_
  unitorL_ = Equiv unitorL_ unitorL

instance Braided x i k => Braided x i (Equiv k) where
  swap = Equiv swap swap
  swap_ = Equiv swap_ swap_

instance Symmetric x i k => Symmetric x i (Equiv k) where

instance (con ~ Obj k, Con' x con, UnCon d con, con i, Compact x i d k, Braided x i k) => Autonomous x i d d (Equiv k) where
  turn = Equiv turn (turn' . swap)
  turn' = Equiv turn' (swap . turn)

instance (con ~ Obj k, Con' x con, UnCon d con, con i, Compact x i d k, Braided x i k) => Compact x i d (Equiv k) where


