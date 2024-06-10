{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
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

instance DistributiveCat (⊗) (⊕) NatTrans where
  distrL = NatTrans  (\case
     (FunctorProd f (FunctorInj1 g)) -> FunctorInj1 (FunctorProd f g)
     (FunctorProd f (FunctorInj2 h)) -> FunctorInj2 (FunctorProd f h))
  distrL' = NatTrans (\case
     (FunctorInj1 (FunctorProd f g)) -> (FunctorProd f (FunctorInj1 g))
     (FunctorInj2 (FunctorProd f h)) -> (FunctorProd f (FunctorInj2 h)))
  distrR = NatTrans (\case
     FunctorProd (FunctorInj2 g) f -> FunctorInj2 (FunctorProd g f)
     FunctorProd (FunctorInj1 g) f -> FunctorInj1 (FunctorProd g f))
  distrR' = NatTrans (\case
     FunctorInj2 (FunctorProd g f) ->FunctorProd (FunctorInj2 g) f 
     FunctorInj1 (FunctorProd g f) ->FunctorProd (FunctorInj1 g) f)


{-
instance DistributiveCat (∘) (⊗) NatTrans where
  distrL = NatTrans (\(Comp x) -> FunctorProd (Comp (fmap prodFst x)) (Comp (fmap prodSnd x)))
  -- distrL' = NatTrans (\(FunctorProd (Comp g) (Comp h)) -> Comp (FunctorProd <$> g <*> h)) -- needs Obj k = Applicative
  distrR = NatTrans (\(Comp (FunctorProd x y)) -> FunctorProd (Comp x) (Comp y))
  distrR' = NatTrans (\(FunctorProd (Comp x) (Comp y)) -> Comp (FunctorProd x y))
-}
