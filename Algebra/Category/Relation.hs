{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Algebra.Category.Relation where

import Algebra.Classes
import Algebra.Types
import Algebra.Category
import Prelude (Bool(..), Eq(..),(&&),flip, ($),(||))

newtype Rel s a b = Rel (a -> b -> s)

indicate :: Ring s => Bool -> s
indicate = \case
  True -> one
  False -> zero

instance Ring s => Category (Rel s) where
  type Obj (Rel s) = Finite
  Rel p . Rel q = Rel (\i j -> sum [p k j * q i k | k <- inhabitants])
  id = Rel (\_ _ -> one)

instance Ring s => Symmetric (⊗) One (Rel s)
instance Ring s => Braided (⊗) One (Rel s) where
  swap = Rel (\(i `Pair` j) (k `Pair` l) -> indicate (i == l && j == k))

instance Ring s => Dagger (Rel s) where
  dagger (Rel r) = Rel (flip r)

instance Ring s => Monoidal (⊗) One (Rel s) where
  unitorR = Rel (\i (i' `Pair` _) -> indicate (i == i'))
  unitorR_ = dagger unitorR
  Rel p ⊗ Rel q = Rel (\(i `Pair` j) (k `Pair` l) -> p i k * q j l)
  assoc = Rel (\((i `Pair` j) `Pair` k) (i' `Pair` (j' `Pair` k')) -> indicate (i == i' && j == j' && k == k'))
  assoc_ = dagger assoc

instance Ring s => Cartesian (⊗) One (Rel s) where
  dis = Rel (\_ _ -> zero)
  dup = Rel (\i (j `Pair` k) -> indicate (i == j || i == k))

instance Ring s => CoCartesian (⊗) One (Rel s) where
  new = dagger dis
  jam = dagger dup

instance Ring s => Monoidal (⊕) Zero (Rel s) where
  Rel p ⊗ Rel q = Rel $ \case
    (Inj1 i) -> \case
      (Inj1 j) -> p i j
      (Inj2 _) -> zero
    (Inj2 i) -> \case
      (Inj1 _) -> zero
      (Inj2 j) -> q i j
  unitorR = Rel (\i (Inj1 j) -> indicate (i == j))
  assoc = Rel $ \case
    (Inj1 (Inj1 i)) -> \case
      Inj1 j -> indicate (i == j)
      _ -> zero
    (Inj1 (Inj2 i)) -> \case
      Inj2 (Inj1 j) -> indicate (i == j)
      _ -> zero
    (Inj2 i) -> \case
      Inj2 (Inj2 j) -> indicate (i == j)
      _ -> zero
  unitorR_ = dagger unitorR
  assoc_ = dagger assoc

instance Ring s => Symmetric (⊕) Zero (Rel s)
instance Ring s => Braided (⊕) Zero (Rel s) where
  swap = Rel $ \case
    (Inj1 i) -> \case
      (Inj1 _) -> zero
      (Inj2 j) -> indicate (i == j)
    (Inj2 i) -> \case
      (Inj2 _) -> zero
      (Inj1 j) -> indicate (i == j)
    
instance Ring s => CoCartesian (⊕) Zero (Rel s) where
  Rel p ▿ Rel q = Rel $ \case
    (Inj1 i) -> \j -> p i j
    (Inj2 i) -> \j -> q i j
  inl = Rel $ \i -> \case
    (Inj1 j) -> indicate (i == j)
    _ -> zero
  inr = Rel $ \i -> \case
    (Inj2 j) -> indicate (i == j)
    _ -> zero
  new = Rel $ \case
  jam = Rel $ \case
    (Inj1 i) -> \j -> indicate (i == j)
    (Inj2 i) -> \j -> indicate (i == j)

instance Ring s => Cartesian (⊕) Zero (Rel s) where
  exl = dagger inl
  exr = dagger inr
  dup = dagger jam
  
