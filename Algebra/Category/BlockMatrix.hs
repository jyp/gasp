{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Algebra.Category.NatTrans where

import Algebra.Category
import Algebra.Category.Objects (Trivial)
import Algebra.Types
import Algebra.Classes
import Prelude ()

data M s a b where
  Zero :: M s a b
  Diag :: s -> M s a a
  (:▵)  :: M s a b -> M s a c ->  M s a (b ⊕ c)
  (:▿)  :: M s b a -> M s c a ->  M s (b ⊕ c) a

instance Ring s => Scalable s (M s a b) where
  s *^ c = case c of
    Zero -> Zero
    Diag x -> Diag (s*x)
    a :▿ b -> scale s a :▿ scale s b
    a :▵ b -> scale s a :▵ scale s b
  
instance Ring s => Category (M s) where
  Zero . _ = Zero
  _ . Zero = Zero
  Diag s . m = s *^ m
  m . Diag s = s *^ m
  (a1 :▵ a2) . b = (a1 . b) :▵ (a2 . b)
  a . (b1 :▿ b2) = (a . b1) :▿ (a . b2)
  (a1 :▿ a2) . (b1 :▵ b2) = a1 . b1 + a2 . b2

  type Obj (M s) = Trivial
  id = Diag one

instance Ring s => Monoidal (⊕) Zero (M s) where
  (⊗) = cartesianCross
  assoc = cartesianAssoc
  assoc_ = cartesianAssoc_
  unitorR = cartesianUnitor
  unitorR_ = cartesianUnitor_

instance Ring s => Symmetric (⊕) Zero (M s) where
instance Ring s => Braided (⊕) Zero (M s) where
  swap = (zero ▵ id) ▿ (id ▵ zero)
instance Ring s => Cartesian (⊕) Zero (M s) where
  (▵) = (:▵)
  dis = Zero
instance Ring s => CoCartesian (⊕) Zero (M s) where
  (▿) = (:▿)
  new = Zero

instance Additive s => Additive (M s a b) where
  zero = Zero
  Zero + a = a
  a + Zero = a
  Diag s + Diag t = Diag (s + t)
  (a :▵ b) + m  = (a + d) :▵ (b + c) where (d,c) = findSplit  m
  (a :▿ b) + m  = (a + d) :▿ (b + c) where (d,c) = findSplit' m
  m  + (a :▵ b) = (a + d) :▵ (b + c) where (d,c) = findSplit  m
  m  + (a :▿ b) = (a + d) :▿ (b + c) where (d,c) = findSplit' m

instance Group s => Group (M s a b) where
  negate = \case
    Zero -> Zero
    Diag d -> Diag (negate d)
    f :▵ g -> negate f :▵ negate g
    f :▿ g -> negate f :▿ negate g

findSplit :: M s a (b ⊕ c) -> (M s a b, M s a c)
findSplit Zero = (Zero,Zero)
findSplit (Diag s) = (Diag s:▿Zero,Zero :▿ Diag s)
findSplit (a :▵ b) = (a,b)
findSplit ((findSplit -> (a1,a2)) :▿ (findSplit -> (b1,b2))) = (a1:▿b1,a2:▿b2)

findSplit' :: M s (b ⊕ c) a -> (M s b a, M s c a)
findSplit' Zero = (Zero,Zero)
findSplit' (Diag s) = (Diag s:▵Zero,Zero :▵ Diag s)
findSplit' (a :▿ b) = (a,b)
findSplit' ((findSplit' -> (a1,a2)) :▵ (findSplit' -> (b1,b2))) = (a1:▵b1,a2:▵b2)


instance Ring s => Dagger (M s) where
  dagger Zero = Zero
  dagger (Diag s) = Diag s
  dagger (a :▿ b) = dagger a :▵ dagger b
  dagger (a :▵ b) = dagger a :▿ dagger b
  
