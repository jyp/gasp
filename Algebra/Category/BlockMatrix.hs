{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
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
module Algebra.Category.BlockMatrix where

import Algebra.Category
import Algebra.Category.Laws
import Algebra.Category.Objects (Trivial,forallSumType)
import Algebra.Types
import Algebra.Classes
import Prelude (Int,Bool(..),Show(..),($),Semigroup(..),error)
import Test.QuickCheck hiding (scale)
import Test.QuickCheck.Property
import Data.Constraint
import Control.Applicative


data M s a b where
  Zero :: M s a b
  Diag :: s -> M s a a
  (:▵)  :: M s a b -> M s a c ->  M s a (b ⊕ c)
  (:▿)  :: M s b a -> M s c a ->  M s (b ⊕ c) a
  EmptyL :: M s Zero a -- no elements
  EmptyR :: M s a Zero -- no elements
  -- EmptyR and EmptyL are there to make the law unitorR . unitorR_ pass
deriving instance Show s => Show (M s a b)

    
instance (Show s, Additive s, TestEqual s) => TestEqual (M s a b) where
  EmptyR =.= _ = property True
  EmptyL =.= _ = property True
  _ =.= EmptyR = property True
  _ =.= EmptyL = property True
  (a :▵ b) =.= c = case findSplit c of
    (a',b') -> (a =.= a') * (b =.= b')
  (a :▿ b) =.= c = case findSplit' c of
    (a',b') -> (a =.= a') * (b =.= b')
  c =.= (a :▵ b) = case findSplit c of
    (a',b') -> (a =.= a') * (b =.= b')
  c =.= (a :▿ b) = case findSplit' c of
    (a',b') -> (a =.= a') * (b =.= b')
  Zero =.= c = testZero c
  c =.= Zero = testZero c
  (Diag x) =.= (Diag y) = x =.= y

testZero :: (Additive s, TestEqual s) => M s a b -> Property
testZero = \case
     EmptyL -> property True
     EmptyR -> property True
     Zero -> property True
     Diag s -> s =.= zero
     a :▵ b -> testZero a * testZero b
     a :▿ b -> testZero a * testZero b

instance Ring s => Scalable s (M s a b) where
  s *^ c = case c of
    EmptyR -> EmptyR
    EmptyL -> EmptyL
    Zero -> Zero
    Diag x -> Diag (s*x)
    a :▿ b -> scale s a :▿ scale s b
    a :▵ b -> scale s a :▵ scale s b
  
instance Ring s => Category (M s) where
  EmptyL . EmptyR = Zero -- adding zero elements together for each position in the matrix
  EmptyR . _ = EmptyR
  _ . EmptyL = EmptyL
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
  (⊗) = cartesianCross -- a potential optimisation is that two diagonals will be a new diagonal. Represent diagonals as (sparse) vectors?
  assoc = cartesianAssoc
  assoc_ = cartesianAssoc_
  unitorR = cartesianUnitor
  unitorR_ = id ▿ new

instance Ring s => Symmetric (⊕) Zero (M s)
instance Ring s => Braided (⊕) Zero (M s) where
  swap = (zero ▵ id) ▿ (id ▵ zero)
instance Ring s => Cartesian (⊕) Zero (M s) where
  (▵) = (:▵)
  dis = EmptyR
  exl = id ▿ Zero
  exr = Zero ▿ id

instance Ring s => CoCartesian (⊕) Zero (M s) where
  (▿) = (:▿)
  new = EmptyL
  inl = id ▵ Zero
  inr = Zero ▵ id

instance Additive s => Additive (M s a b) where
  zero = Zero
  Zero + a = a
  a + Zero = a
  EmptyL + _ = EmptyL
  _ + EmptyL = EmptyL
  EmptyR + _ = EmptyR
  _ + EmptyR = EmptyR
  (a :▵ b) + m  = (a + d) :▵ (b + c) where (d,c) = findSplit  m
  m  + (a :▵ b) = (a + d) :▵ (b + c) where (d,c) = findSplit  m
  (a :▿ b) + m  = (a + d) :▿ (b + c) where (d,c) = findSplit' m
  m  + (a :▿ b) = (a + d) :▿ (b + c) where (d,c) = findSplit' m
  Diag s + Diag t = Diag (s + t)

instance Group s => Group (M s a b) where
  negate = \case
    EmptyL -> EmptyL
    EmptyR -> EmptyR
    Zero -> Zero
    Diag d -> Diag (negate d)
    f :▵ g -> negate f :▵ negate g
    f :▿ g -> negate f :▿ negate g

findSplit :: M s a (b ⊕ c) -> (M s a b, M s a c)
findSplit EmptyL = (EmptyL, EmptyL)
findSplit Zero = (Zero,Zero)
findSplit (Diag s) = (Diag s:▿Zero,Zero :▿ Diag s)
findSplit (a :▵ b) = (a,b)
findSplit ((findSplit -> (a1,a2)) :▿ (findSplit -> (b1,b2))) = (a1:▿b1,a2:▿b2)

findSplit' :: M s (b ⊕ c) a -> (M s b a, M s c a)
findSplit' EmptyR = (EmptyR, EmptyR)
findSplit' Zero = (Zero,Zero)
findSplit' (Diag s) = (Diag s:▵Zero,Zero :▵ Diag s)
findSplit' (a :▿ b) = (a,b)
findSplit' ((findSplit' -> (a1,a2)) :▵ (findSplit' -> (b1,b2))) = (a1:▵b1,a2:▵b2)


transpose :: M s a b -> M s b a
transpose = \case
  EmptyL -> EmptyR
  EmptyR -> EmptyL
  Zero -> Zero
  (Diag s) -> Diag s
  (a :▿ b) -> transpose a :▵ transpose b
  (a :▵ b) -> transpose a :▿ transpose b

genMorphism :: Arbitrary s => Ring s => Repr (⊗) One (⊕) Zero a -> Repr (⊗) One (⊕) Zero b -> Gen (M s a b)
genMorphism RZero _ = pure EmptyL
genMorphism _ RZero = pure EmptyR
genMorphism (RPlus x y) b = transpose <$> ((▵) <$> (genMorphism b x) <*> (genMorphism b y))
genMorphism ROne (RPlus x y) = (▵) <$> genMorphism ROne x <*> genMorphism ROne y
genMorphism ROne ROne = Diag <$> arbitrary
genMorphism x _ = error ("genMorphism: " <> show x)


prop_block_matrix :: Property
prop_block_matrix =
  laws_bicartesian @(M Int)
  (testableCat
     (\k -> forallSumType @(⊗) @One @(⊕) @Zero (\t -> k t))
     (\tx ty k -> property $ do
         x <- genMorphism tx ty
         unProperty (k x))
     (\_ _ -> Dict)
     RPlus
     RZero)
