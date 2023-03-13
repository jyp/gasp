{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Algebra.Types.Arbitrary where

import Test.QuickCheck
import Algebra.Types
import Data.Kind

data Some1 f where
  Some1 :: f x -> Some1 f


data Repr :: k -> Type where
  RPlus :: Repr a -> Repr b -> Repr (a ⊕ b)
  RTimes :: Repr a -> Repr b -> Repr (a ⊗ b)
  ROne :: Repr One
  RZero :: Repr Zero



sizedArbRepr :: Int -> Gen (Some1 Repr)
sizedArbRepr n
  | n <= 1 = frequency [(1,pure(Some1 RZero)), (3,pure(Some1 ROne))]
  | otherwise = do
      Some1 l <- sizedArbRepr (n `div` 2)
      Some1 r <- sizedArbRepr (n `div` 2)
      elements [Some1 (RPlus l r),Some1 (RTimes l r)]
  
instance Arbitrary (Some1 Repr) where
  arbitrary = sized sizedArbRepr

arbitraryF1 :: Gen (Some1 repr) -> (forall x. repr x -> Gen (f x)) -> (forall x. f x -> prop) -> Gen prop
arbitraryF1 r g p = do
  Some1 a <- r
  b <- g a
  return (p b)
  
arbitraryF2 :: Gen (Some1 repr) -> Gen (Some1 repr) -> (forall x y. repr x -> repr y -> Gen (f x y)) -> (forall x y. f x y -> prop) -> Gen prop
arbitraryF2 r1 r2 g p = do
  Some1 a <- r1
  Some1 a' <- r2
  b <- g a a'
  return (p b)
