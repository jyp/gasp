{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Algebra.Category.NatTrans where

import Algebra.Category
import Prelude (Functor(..))
import Algebra.Types

import Data.Kind

newtype NatTrans (f :: Type -> Type) (g :: Type -> Type) = NatTrans (forall x. f x -> g x)

instance Category NatTrans where
  type Obj NatTrans = Functor
  NatTrans f . NatTrans g = NatTrans (f ∘ g)
  id = NatTrans id

instance Monoidal (∘) Id NatTrans where
  assoc_ = NatTrans (Comp . Comp . fmap fromComp . fromComp)
  unitorR_ = NatTrans (fmap fromId . fromComp)
  NatTrans f ⊗ NatTrans g = NatTrans (Comp . f . fmap g . fromComp)
  assoc =  NatTrans (Comp . fmap Comp . fromComp . fromComp)
  unitorR = NatTrans (Comp . fmap Id)
  unitorL = NatTrans (Comp . Id)
  unitorL_ = NatTrans (fromId . fromComp)

instance Monoidal (⊗) One NatTrans where
  assoc = NatTrans (\(FunctorProd (FunctorProd x y) z) -> FunctorProd x (FunctorProd y z))
  assoc_ = NatTrans (\(FunctorProd x (FunctorProd y z)) -> (FunctorProd (FunctorProd x y) z))
  unitorR = NatTrans (\x -> FunctorProd x FunctorOne)
  unitorR_ = NatTrans (\(FunctorProd x _) -> x)
  unitorL = NatTrans (FunctorProd FunctorOne)
  unitorL_ = NatTrans (\(FunctorProd _ x) -> x)
  NatTrans f ⊗ NatTrans g = NatTrans (\(FunctorProd x y) ->  FunctorProd (f x) (g y))
  
