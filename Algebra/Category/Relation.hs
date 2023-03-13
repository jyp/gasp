{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Algebra.Category.Relation where

import Algebra.Classes
import Algebra.Types
import Algebra.Category

import Prelude (Bool(..), Eq(..),(&&),flip)
newtype Rel s a b = Rel (a -> b -> s)

indicate :: Ring s => Bool -> s
indicate = \case
  True -> one
  False -> zero

instance Ring s => Category (Rel s) where
  type Obj (Rel s) = Finite
  Rel p . Rel q = Rel (\i j -> sum [p k j * q i k | k <- inhabitants])
  id = Rel (\_ _ -> one)

instance Ring s => Braided (Rel s) where
  swap = Rel (\(i `Pair` j) (k `Pair` l) -> indicate (i == l && j == k))

instance Ring s => Dagger (Rel s) where
  dagger (Rel r) = (Rel (flip r))

instance Ring s => Monoidal (Rel s) where
  unitorR = Rel (\i (i' `Pair` _) -> indicate (i == i'))
  unitorR_ = dagger unitorR
  Rel p ⊗ Rel q = Rel (\(i `Pair` j) (k `Pair` l) -> p i k * q j l)
  assoc = Rel (\((i `Pair` j) `Pair` k) (i' `Pair` (j' `Pair` k')) -> indicate (i == i' && j == j' && k == k'))
  assoc_ = dagger assoc
