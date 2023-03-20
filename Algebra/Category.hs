{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
module Algebra.Category where

import Algebra.Classes (nameLaw, TestEqual(..), product)
import Algebra.Types
import Algebra.Category.Objects
import qualified Prelude
import Data.Kind
import Data.Constraint
import Test.QuickCheck
import Prelude (Show(..))
import qualified Algebra.CategoryRecords as R

type O2 k a b = (Obj k a, Obj k b)
type O3 k a b c =
  (Obj k a, Obj k b, Obj k c)
type O4 k a b c d =
  (Obj k a, Obj k b, Obj k c, Obj k d)

infixr 9 .

  
-- | A class for categories. Instances should satisfy the laws
--
-- @
-- f '.' 'id'  =  f  -- (right identity)
-- 'id' '.' f  =  f  -- (left identity)
-- f '.' (g '.' h)  =  (f '.' g) '.' h  -- (associativity)
-- @

class Category (cat :: k -> k -> Type) where
  type Obj (cat) :: k -> Constraint
  (.)      :: (Obj cat a, Obj cat b, Obj cat c) => b `cat` c -> a `cat` b -> a `cat` c
  id :: Obj cat a => a `cat` a


-- , (∘) = (∘), id = id


class Category cat => Dagger cat where
  dagger :: O2 cat a b => a `cat` b -> b `cat` a

(∘) :: forall {k} (cat :: k -> k -> Type) a b c con. (Category cat, con ~ Obj cat, con a, con b, con c) => cat b c -> cat a b -> cat a c
(∘) = (.) 

type Monoidal :: forall {k}. (k -> k -> k) -> k -> (k -> k -> Type) -> Constraint

class ({-ProdObj (Obj cat), -}Category cat) => Monoidal x i (cat :: k -> k -> Type) | x -> i, i -> x where
  (⊗)      :: (Obj cat a, Obj cat b, Obj cat c, Obj cat d) => (a `cat` b) -> (c `cat` d) -> (a `x` c) `cat` (b `x` d)
  assoc    :: (Obj cat a, Obj cat b, Obj cat c) => ((a `x` b) `x` c) `cat` (a `x` (b `x` c))
  assoc_   :: (Obj cat a, Obj cat b, Obj cat c) => (a `x` (b `x` c)) `cat` ((a `x` b) `x` c)
  unitorR   :: (Obj cat a) => a `cat` (a `x` i)
  unitorR_  :: (Obj cat a) => (a `x` i) `cat` a
  unitorL   :: forall a. (Obj cat a, Obj cat i) => a `cat` (i `x` a)
  unitorL_  :: (Obj cat a, Obj cat i) => (i `x` a) `cat` a

  default unitorL :: forall a con. (con ~ Obj cat, con i, Con' x con, Symmetric x i cat, Obj cat a) => a `cat` (i `x` a)
  unitorL = swap ∘ unitorR
  default unitorL_ :: forall a con. (con ~ Obj cat, Symmetric x i cat, con i, Con' x con, Obj cat a) => (i `x` a) `cat` a 
  unitorL_ = unitorR_ ∘ swap

monoidalRec :: forall x cat i. Monoidal x i cat => R.MonoidalRec x i (Obj cat) cat
monoidalRec = R.MonoidalRec { (⊗) = (⊗), assoc = assoc, assoc_ = assoc_,   unitorR = unitorR, unitorL = unitorL, unitorL_ = unitorL_, unitorR_ = unitorR_}



class Monoidal x i cat => Braided x i cat where
  swap     :: (Obj cat a, Obj cat b) => (a `x` b) `cat` (b `x` a)
  swap_     :: (Obj cat a, Obj cat b) => (a `x` b) `cat` (b `x` a)
  default swap_ :: (Symmetric x i cat, Obj cat a, Obj cat b) => (a `x` b) `cat` (b `x` a)
  swap_ = swap

braidedRec :: forall x cat i. Braided x i cat => R.BraidedRec x i (Obj cat) cat
braidedRec = R.BraidedRec { swap = swap, swap_ = swap_}


class Braided x i cat => Symmetric x i cat



class Symmetric x i cat => Cartesian x i cat where
  {-# MINIMAL exl,exr,dup | exl,exr,(▵) | dis,dup | dis,(▵) #-}
  exl   ::   forall a b. O2 cat a b                     =>    (a `x` b) `cat` a
  exr   ::   forall a b. O2 cat a b                     =>    (a `x` b) `cat` b
  dis   ::   forall a.  Obj cat a                       =>    a `cat` i
  dup   ::   forall a. Obj cat a                        =>    a `cat` (a `x` a)
  (▵)   ::   forall a b c. (Obj cat a,Obj cat b, Obj cat c) =>    (a `cat` b) -> (a `cat` c) -> a `cat` (b `x` c)
  default dis :: forall a con. (con ~ Obj cat, con i, Con' x con, Obj cat a) => a `cat` i
  dis = exr . unitorR
  default dup :: forall a con. (con ~ Obj cat, con i, Con' x con, Obj cat a) => a `cat` (a `x` a)
  dup = id ▵ id
  default exl :: forall a b con. (con ~ Obj cat, con i, Con' x con, con a, con b) =>  (a `x` b) `cat` a
  exl = unitorR_ . (id ⊗ dis)
  default exr :: forall a b con. (con ~ Obj cat, con i, Con' x con, con a, con b) =>  (a `x` b) `cat` b
  exr = unitorL_ ∘ (dis ⊗ id)
  default (▵)   ::   forall a b c con. (con ~ Obj cat, con i, Con' x con, Obj cat a,Obj cat b, Obj cat c) =>    (a `cat` b) -> (a `cat` c) -> a `cat` (b `x` c)
  f ▵ g = (f ⊗ g) ∘ dup 

cartesianRec :: forall x cat i. Cartesian x i cat => R.CartesianRec x i (Obj cat) cat
cartesianRec = R.CartesianRec {exl = exl , exr = exr , dis = dis , dup = dup , (▵) = (▵)}

cartesianCross :: (Obj k (b1 `x` b2), Obj k b3, Obj k c, Obj k b1, Obj k b2, Cartesian x i k) => k b1 b3 -> k b2 c -> k (b1 `x` b2) (b3 `x` c)
cartesianCross a b = (a . exl) ▵ (b . exr)

cartesianUnitor :: forall a k x i. (Obj k a, Obj k i, Cartesian x i k) => a `k` (a `x` i)
cartesianUnitor = id ▵ dis
cartesianUnitor_ :: forall a k x i. (Obj k a, Obj k i, Cartesian x i k) => (a `x` i) `k` a
cartesianUnitor_ = exl
cartesianSwap :: forall a b k x i con. (Obj k a, Obj k b, Cartesian x i k, Con' x con, con ~ Obj k) => (a `x` b) `k` (b `x` a)
cartesianSwap = exr ▵ exl
cartesianAssoc :: forall a b x i c k con. (Obj k a, Obj k b, Obj k c, Cartesian x i k, Con' x con, con ~ Obj k) => ((a `x` b) `x` c) `k` (a `x` (b `x` c))
cartesianAssoc = (exl . exl) ▵ ((exr . exl) ▵ exr)
cartesianAssoc_ :: forall a b x i c k con. (Obj k a, Obj k b, Obj k c, Cartesian x i k, Con' x con, con ~ Obj k) => (a `x` (b `x` c)) `k` ((a `x` b) `x` c)
cartesianAssoc_ = (exl ▵ (exl . exr)) ▵ (exr . exr)



class Symmetric x i cat => CoCartesian x i cat where
  {-# MINIMAL inl,inr,jam | inl,inr,(▿) | new,jam | new,(▿) #-}
  inl   ::  O2 cat a b                                 =>  a `cat` (a `x` b)
  inr   ::  O2 cat a b                                 =>  b `cat` (a `x` b)
  new   ::  forall a. (Obj cat a)                      =>  i `cat` a
  jam   ::  Obj cat a                                  =>  (a `x` a) `cat` a
  (▿)    ::  forall a b c. (Obj cat a,Obj cat b, Obj cat c) =>  (b `cat` a) -> (c `cat` a) -> (b `x` c) `cat` a
  default new :: forall a con. (con ~ Obj cat, con i, Con' x con, Obj cat a) => i `cat` a 
  new = unitorR_ . inr
  default jam :: forall a con. (con ~ Obj cat, con i, Con' x con, Obj cat a) => (a `x` a) `cat` a 
  jam = id ▿ id
  default inl :: forall a b con. (con ~ Obj cat, con i, Con' x con, con a, con b) => a `cat` (a `x` b) 
  inl = (id ⊗ new) . unitorR 
  default inr :: forall a b con. (con ~ Obj cat, con i, Con' x con, con a, con b) => b `cat`  (a `x` b)
  inr = (new ⊗ id) ∘ unitorL
  default (▿)   ::   forall a b c con. (con ~ Obj cat, con i, Con' x con, Obj cat a,Obj cat b, Obj cat c) =>    (b `cat` a) -> (c `cat` a) -> (b `x` c) `cat` a
  f ▿ g = jam ∘ (f ⊗ g) 

type BiCartesian x i cat = (Cartesian x i cat, CoCartesian x i cat)

class Monoidal x i cat => Autonomous l r x i cat | x -> l, x -> r where
  turn   :: i `cat` (l a ⊗ a)
  turn'  :: (a ⊗ r a) `cat` i
  
class (Symmetric x i cat, Autonomous d d x i cat) => Compact x d i cat where

  

---------------------------
-- Instances
----------------------------

instance Category (->) where
  type Obj (->) = Trivial
  (.) = (Prelude..)
  id = Prelude.id

instance Monoidal (⊗) One (->) where
  (f ⊗ g) (x `Pair` y) = (f x `Pair` g y)
  assoc ((x `Pair` y) `Pair` z) = (x `Pair` (y `Pair` z)) 
  assoc_ (x `Pair` (y `Pair` z)) = ((x `Pair` y) `Pair` z)  
  unitorR x = (x `Pair` Unit)
  unitorR_ (x `Pair` Unit) = x

instance Braided (⊗) One (->) where
  swap (x `Pair` y) = (y `Pair` x)
instance Symmetric (⊗) One (->)

instance Monoidal (⊕) Zero (->) where
  f ⊗ g = \case
    Inj1 x -> Inj1 (f x)
    Inj2 x -> Inj2 (g x)
  assoc = \case
    Inj1 (Inj1 x) -> Inj1 x
    Inj1 (Inj2 x) -> Inj2 (Inj1 x)
    Inj2 x -> Inj2 (Inj2 x)
  assoc_ = \case
    (Inj1 x) -> (Inj1 (Inj1 x)) 
    (Inj2 (Inj1 x)) -> (Inj1 (Inj2 x)) 
    (Inj2 (Inj2 x)) -> (Inj2 x) 
  unitorR = Inj1
  unitorL = Inj2
  unitorR_ = \case
    Inj1 x -> x
    Inj2 x -> case x of

instance Symmetric (⊕) Zero (->) where
instance Braided (⊕) Zero (->) where
  swap = \case
    Inj1 x -> Inj2 x
    Inj2 x -> Inj1 x

instance Cartesian (⊗) One (->) where
  dup x = Pair x x
  exr (Pair _ x) = x
  exl (Pair x _) = x
  (f ▵ g) x = f x `Pair` g x
  dis _ = Unit

instance CoCartesian (⊕) Zero (->) where
  inl = Inj1
  inr = Inj2
  new = \case
  f ▿ g = \case
     Inj1 x -> f x
     Inj2 y -> g y
  jam = \case
     Inj1 x -> x
     Inj2 x -> x

