{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Algebra.Category.Objects where

import Algebra.Classes
import Algebra.Types
import Prelude (Int, Ord (..),otherwise,($),Show, Semigroup(..),show)
import Data.Kind
import Data.Constraint
import Test.QuickCheck
import Test.QuickCheck.Property
import Control.Applicative

type TimesCon con = forall a b. (con a, con b) => con (a⊗b) :: Constraint
type PlusCon con = forall a b. (con a, con b) => con (a⊕b) :: Constraint
type Con' x con = forall a b. (con a, con b) => con (a `x` b) :: Constraint

type TimesCon1 con = forall x a b. (con (a (b x))) => con ((a⊗b) x) :: Constraint
type PlusCon1 con = forall x a b. (con (a x), con (b x)) => con ((a⊕b) x) :: Constraint
type OneCon1 (con :: Type -> Constraint) = forall x. con x => con (One x) :: Constraint
type ZeroCon1 con = forall x. con x => con (Zero x) :: Constraint
-- type LConTensor con = forall a b. con (a⊗b) => con a :: Constraint
-- type RConTensor con = forall a b. con (a⊗b) => con a :: Constraint

reprCon :: forall con a x i t o. (Con' x con, Con' t con, con i, con o) => Repr x i t o a -> Dict (con a)
reprCon = \case
  RPlus a b -> Dict \\ reprCon @con a \\ reprCon @con b
  RTimes a b -> Dict \\ reprCon @con a \\ reprCon @con b
  RZero -> Dict
  ROne -> Dict

reprCon1Comp :: forall (z :: Type) con (a :: Type -> Type) b. CompClosed con -> con z => CRepr a -> CRepr b -> Dict (con (a (b z)))
reprCon1Comp c@CompClosed{..} a b = Dict \\ reprCon1 @(b z) c a \\ reprCon1 @z c b

reprCon1 :: forall (z :: Type) (con :: Type -> Constraint) a. con z => CompClosed con -> CRepr a -> Dict (con (a z))
reprCon1 c@CompClosed{..} = \case
  RPlus a b -> plus1Closed \\ reprCon1 @z c a \\ reprCon1 @z c b
  RTimes a b -> times1Closed \\ reprCon1Comp @z c a b
  RZero -> zero1Closed
  ROne -> one1Closed
{-


type ProdObj :: forall {k}. (k -> Constraint) -> Constraint
class ProdObj (con :: k -> Constraint) where -- TensorClosed constraint causes problems in the Free module. (probabjy GHC bug)
  objprod :: (con a, con b) => Dict (con (a⊗b))
  objfstsnd :: forall z a b. (z ~ (a⊗b), con z) => Dict (con a, con b)
  objone :: Dict (con One)


type SumObj :: forall {k}. (k -> Constraint) -> Constraint
class SumObj (con :: k -> Constraint) where -- TensorClosed constraint causes problems in the Free module. (probabjy GHC bug)
  objsum :: (con a, con b) => Dict (con (a⊕b))
  objleftright :: forall z a b. (z ~ (a⊕b), con z) => Dict (con a, con b)
  objzero :: Dict (con Zero)


objSumProxy :: (SumObj con, con a, con b) => proxy1 a -> proxy2 b -> Dict (con (a⊕b))
objSumProxy _ _  = objsum

objProdProxy :: (ProdObj con, con a, con b) => proxy1 a -> proxy2 b -> Dict (con (a⊗b))
objProdProxy _ _  = objprod

instance ProdObj Trivial where
  objprod = Dict
  objfstsnd = Dict
  objone = Dict

instance SumObj Trivial where
  objsum = Dict
  objleftright = Dict
  objzero = Dict

instance ProdObj Finite where
  objprod = Dict
  objfstsnd = finiteFstsnd
  objone = Dict

instance SumObj Finite where
  objsum = Dict
  objleftright = finiteLeftRight
  objzero = Dict

-}

type Trivial :: k -> Constraint
class Trivial x
instance Trivial x



data Some1  f where
  Some1 :: f x -> Some1 f

sizedArbRepr :: Int -> Gen (Some1 (Repr x i t o))
sizedArbRepr n
  | n <= 1 = frequency [(1,pure(Some1 RZero)), (3,pure(Some1 ROne))]
  | otherwise = do
      Some1 l <- sizedArbRepr  (n `div` 2)
      Some1 r <- sizedArbRepr  (n `div` 2)
      elements [Some1 (RPlus l r),Some1 (RTimes l r)]

sizedArbSum :: Int -> Gen (Some1 (Repr x i t o))
sizedArbSum n
  | n <= 1 = frequency [(1,pure(Some1 RZero)), (3,pure(Some1 ROne))]
  | otherwise = do
      Some1 l <- sizedArbSum  (n `div` 2)
      Some1 r <- sizedArbSum  (n `div` 2)
      elements [Some1 (RPlus l r)]


isArbitrary1 :: CRepr x -> Dict (Arbitrary1 x)
isArbitrary1 = reprCon

isCoArbitrary :: MRepr x -> Dict (CoArbitrary x)
isCoArbitrary = reprCon

instance Arbitrary (Some1 (Repr x i t o)) where
  arbitrary = sized sizedArbRepr

forallSumType :: forall {k} x i t o. (forall (a :: k). Repr x i t o a -> Property) -> Property
forallSumType gen = MkProperty $ do
  Some1 t <- (sized sizedArbSum :: Gen (Some1 (Repr x i t o)))
  unProperty (counterexample ("obj: " <> show t) (property (gen t)))

forallType :: forall {k} x i t o. (forall (a :: k). Repr x i t o a -> Property) -> Property
forallType gen = MkProperty $ do
  Some1 t <- (arbitrary :: Gen (Some1 (Repr x i t o)))
  unProperty (counterexample ("obj: " <> show t) (property (gen t)))



arbitrary2' :: forall f a b proxy. Arbitrary (f a b) => proxy a -> proxy b -> Gen (f a b)
arbitrary2' _ _ = arbitrary

forallMorphism :: forall f a b x i t o. (Show (f a b), Arbitrary (f a b))
               => Repr x i t o a -> Repr x i t o b -> (f a b -> Property) -> Property
forallMorphism t1 t2 = forAll (arbitrary2' t1 t2)

