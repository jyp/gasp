{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Algebra.Category.NatTrans where

import Algebra.Category
import Prelude (Functor(..),flip)
import Algebra.Types

import Data.Kind

newtype NatTrans (f :: Type -> Type) (g :: Type -> Type) = NatTrans (forall x. f x -> g x)


instance Category NatTrans where
  type Obj NatTrans = Functor
  NatTrans f . NatTrans g = NatTrans (f ∘ g)
  id = NatTrans id

instance Monoidal NatTrans where
  assoc_ = NatTrans (Comp . Comp . fmap fromComp . fromComp)
  unitorR_ = NatTrans (fmap fromFunctorUnit . fromComp)
  NatTrans f ⊗ NatTrans g = NatTrans (\(Comp x) -> Comp (f (fmap g x)))
  assoc =  NatTrans (\(Comp (Comp x)) -> Comp (fmap Comp x))
  unitorR = NatTrans (\x -> Comp (fmap FunctorUnit x))
  unitorL = NatTrans (Comp . FunctorUnit)
  unitorL_ = NatTrans (fromFunctorUnit . fromComp)

instance Monoidal' NatTrans where
  assoc' = NatTrans (\(FunctorProd (FunctorProd x y) z) -> FunctorProd x (FunctorProd y z))
  assoc_' = NatTrans (\(FunctorProd x (FunctorProd y z)) -> (FunctorProd (FunctorProd x y) z))
  unitorR' = NatTrans (\x -> FunctorProd x FunctorZero)
  unitorR_' = NatTrans (\(FunctorProd x _) -> x)
  unitorL' = NatTrans (FunctorProd FunctorZero)
  unitorL_' = NatTrans (\(FunctorProd _ x) -> x)
  NatTrans f ⊕ NatTrans g = NatTrans (\(FunctorProd x y) ->  FunctorProd (f x) (g y))
  


newtype FMat x f g = FMat (f (g x))
