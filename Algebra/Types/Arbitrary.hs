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
  ROne :: Repr One
  RZero :: Repr Zero



sizedArbRepr :: Int -> Gen (Some1 Repr)
sizedArbRepr n
  | n <= 1 = frequency [(1,pure(Some1 RZero)), (3,pure(Some1 ROne))]
  | otherwise = 
  
-- sizedArbRepr n = do
--   es <- vectorOf 2 (sizedArbRepr (n-1))
--   elements [R es, RTimes es]
  
instance Arbitrary (Some1 Repr) where
  arbitrary = _

arbitrary1 :: Gen (Some1 f) -> (forall x. f x -> prop) -> Gen prop
arbitrary1 g f = do
  Some1 a <- g
  return (f a)
