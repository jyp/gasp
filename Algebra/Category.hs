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

import Algebra.Types
import qualified Prelude
import Data.Kind
import Data.Constraint

-- | A class for categories. Instances should satisfy the laws
--
-- @
-- f '.' 'id'  =  f  -- (right identity)
-- 'id' '.' f  =  f  -- (left identity)
-- f '.' (g '.' h)  =  (f '.' g) '.' h  -- (associativity)
-- @

type Trivial :: k -> Constraint
class Trivial x
instance Trivial x

instance ProdObj Trivial where
  objprod = Dict
  objfstsnd = Dict
  objunit = Dict

instance SumObj Trivial where
  objsum = Dict
  objleftright = Dict
  objzero = Dict

instance ProdObj Finite where
  objprod = Dict
  objfstsnd = finiteFstsnd
  objunit = Dict

instance SumObj Finite where
  objsum = Dict
  objleftright = finiteLeftRight
  objzero = Dict


type O2 k a b = (Obj k a, Obj k b)
type O3 k a b c =
  (Obj k a, Obj k b, Obj k c)
type O4 k a b c d =
  (Obj k a, Obj k b, Obj k c, Obj k d)

infixr 9 .

class Category (cat :: k -> k -> Type) where
  type Obj (cat) :: k -> Constraint
  (.)      :: (Obj cat a, Obj cat b, Obj cat c) => b `cat` c -> a `cat` b -> a `cat` c
  id :: Obj cat a => a `cat` a

class Category cat => Dagger cat where
  dagger :: O2 cat a b => a `cat` b -> b `cat` a

(∘) :: forall {k} (cat :: k -> k -> Type) a b c con. (Category cat, con ~ Obj cat, con a, con b, con c) => cat b c -> cat a b -> cat a c
(∘) = (.) 

type ProdObj :: forall {k}. (k -> Constraint) -> Constraint
class ProdObj (con :: k -> Constraint) where -- TensorClosed constraint causes problems in the Free module. (probabjy GHC bug)
  objprod :: (con a, con b) => Dict (con (a⊗b))
  objfstsnd :: forall z a b. (z ~ (a⊗b), con z) => Dict (con a, con b)
  objunit :: Dict (con One)


class (ProdObj (Obj cat), Category cat) => Monoidal (cat :: k -> k -> Type) where
  (⊗)      :: (Obj cat a, Obj cat b, Obj cat c, Obj cat d) => (a `cat` b) -> (c `cat` d) -> (a ⊗ c) `cat` (b ⊗ d)
  assoc    :: (Obj cat a, Obj cat b, Obj cat c) => ((a ⊗ b) ⊗ c) `cat` (a ⊗ (b ⊗ c))
  assoc_   :: (Obj cat a, Obj cat b, Obj cat c) => (a ⊗ (b ⊗ c)) `cat` ((a ⊗ b) ⊗ c)
  unitorR   :: (Obj cat a) => a `cat` (a ⊗ One)
  unitorR_  :: (Obj cat a) => (a ⊗ One) `cat` a
  unitorL   :: (Obj cat a, Obj cat One) => a `cat` (One ⊗ a)
  unitorL_  :: (Obj cat a, Obj cat One) => (One ⊗ a) `cat` a

  default unitorL :: forall a. (Braided cat, Obj cat a) => a `cat` (One ⊗ a)
  unitorL = swap ∘ unitorR
     \\ objprod @(Obj cat) @a @One
     \\ objprod @(Obj cat) @One @a
     \\ objunit @(Obj cat)

  default unitorL_ :: forall a. (Braided cat, Obj cat a) => (One ⊗ a) `cat` a 
  unitorL_ = unitorR_ ∘ swap
     \\ objprod @(Obj cat) @a @One
     \\ objprod @(Obj cat) @One @a
     \\ objunit @(Obj cat)


class Monoidal cat => Braided cat where
  swap     :: (Obj cat a, Obj cat b) => (a ⊗ b) `cat` (b ⊗ a)

class Monoidal k => Cartesian k where
  exl   ::   forall a b. O2 k a b                     =>    (a ⊗ b) `k` a
  exr   ::   forall a b. O2 k a b                     =>    (a ⊗ b) `k` b
  dis   ::   forall a.  Obj k a                      =>    a `k` One
  dup   ::   forall a. Obj k a                   =>    a `k` (a ⊗ a)
  (▵)   ::   forall a b c. (Obj k a,Obj k b, Obj k c) =>    (a `k` b) -> (a `k` c) -> a `k` (b ⊗ c)

  {-# MINIMAL exl,exr,dup | exl,exr,(▵) | dis,dup | dis,(▵) #-}
  dis = exr . unitorR
     \\ objprod @(Obj k) @a @One
     \\ objunit @(Obj k)
  dup = id ▵ id
  exl = unitorR_ . (id ⊗ dis)
          \\ objprod @(Obj k) @a @b
          \\ objprod @(Obj k) @a @One
          \\ objunit @(Obj k)
  exr = unitorL_ ∘ (dis ⊗ id)
          \\ objprod @(Obj k) @a @b
          \\ objprod @(Obj k) @One @b
          \\ objunit @(Obj k)
  f ▵ g = (f ⊗ g) ∘ dup 
          \\ objprod @(Obj k) @a @a
          \\ objprod @(Obj k) @b @c 

cartesianCross :: (Obj k (b1 ⊗ b2), Obj k b3, Obj k c, Obj k b1,
                     Obj k b2, Cartesian k) =>
                    k b1 b3 -> k b2 c -> k (b1 ⊗ b2) (b3 ⊗ c)
cartesianCross a b = (a . exl) ▵ (b . exr)


type TensorCon con = forall a b. (con a, con b) => con (a⊗b) :: Constraint
type LConTensor con = forall a b. con (a⊗b) => con a :: Constraint
type RConTensor con = forall a b. con (a⊗b) => con a :: Constraint

type SumObj :: forall {k}. (k -> Constraint) -> Constraint
class SumObj (con :: k -> Constraint) where -- TensorClosed constraint causes problems in the Free module. (probabjy GHC bug)
  objsum :: (con a, con b) => Dict (con (a⊕b))
  objleftright :: forall z a b. (z ~ (a⊕b), con z) => Dict (con a, con b)
  objzero :: Dict (con Zero)

class (SumObj (Obj cat), Category cat) => Monoidal' (cat :: k -> k -> Type) where
  (⊕)      :: (Obj cat a, Obj cat b, Obj cat c, Obj cat d) => (a `cat` b) -> (c `cat` d) -> (a ⊕ c) `cat` (b ⊕ d)
  assoc'    :: (Obj cat a, Obj cat b, Obj cat c) => ((a ⊕ b) ⊕ c) `cat` (a ⊕ (b ⊕ c))
  assoc_'   :: (Obj cat a, Obj cat b, Obj cat c) => (a ⊕ (b ⊕ c)) `cat` ((a ⊕ b) ⊕ c)
  unitorR'   :: (Obj cat a) => a `cat` (a ⊕ Zero)
  unitorR_'  :: (Obj cat a) => (a ⊕ Zero) `cat` a
  unitorL'   :: (Obj cat a, Obj cat Zero) => a `cat` (Zero ⊕ a)
  unitorL_'  :: (Obj cat a, Obj cat Zero) => (Zero ⊕ a) `cat` a

  default unitorL' :: forall a. (Braided' cat, Obj cat a) => a `cat` (Zero ⊕ a)
  unitorL' = swap' ∘ unitorR'
     \\ objsum @(Obj cat) @a @Zero
     \\ objsum @(Obj cat) @Zero @a
     \\ objzero @(Obj cat)

  default unitorL_' :: forall a. (Braided' cat, Obj cat a) => (Zero ⊕ a) `cat` a 
  unitorL_' = unitorR_' ∘ swap' 
     \\ objsum @(Obj cat) @a @Zero
     \\ objsum @(Obj cat) @Zero @a
     \\ objzero @(Obj cat)



class Monoidal' cat => Braided' cat where
  swap'     :: (Obj cat a, Obj cat b) => (a ⊕ b) `cat` (b ⊕ a)

type Cartesian' :: forall {k}. (k -> k -> Type) -> Constraint
class Monoidal' cat => Cartesian' cat where
  exl'  ::   forall a b. O2 cat a b                     =>    (a ⊕ b) `cat` a
  exr'  ::   forall a b. O2 cat a b                     =>    (a ⊕ b) `cat` b
  dis'  ::   forall a.   Obj cat a                      =>    a `cat` Zero
  dup'  ::   (Obj cat a, Obj cat (a⊕a))                   =>    a `cat` (a ⊕ a)
  (▴)   ::   forall a b c. (Obj cat a,Obj cat b, Obj cat c) =>    (a `cat` b) -> (a `cat` c) -> a `cat` (b ⊕ c)

  {-# MINIMAL exl',exr',dup' | exl',exr',(▴) | dis',dup' | dis',(▴) #-}
  dis' = exr' . unitorR'
     \\ objsum @(Obj cat) @a @Zero
     \\ objzero @(Obj cat)
  dup' = id ▴ id
  exl' = unitorR_' . (id ⊕ dis')
          \\ objsum @(Obj cat) @a @b
          \\ objsum @(Obj cat) @a @Zero
          \\ objzero @(Obj cat)
  exr' = unitorL_' ∘ (dis' ⊕ id)
          \\ objsum @(Obj cat) @a @b
          \\ objsum @(Obj cat) @Zero @b
          \\ objzero @(Obj cat)
  f ▴ g = (f ⊕ g) ∘ dup' 
          \\ objsum @(Obj cat) @a @a
          \\ objsum @(Obj cat) @b @c 


class Monoidal' k => CoCartesian' k where
  inl'   ::  O2 k a b                                 =>  a `k` (a ⊕ b)
  inr'   ::  O2 k a b                                 =>  b `k` (a ⊕ b)
  new'   ::  forall a. (Obj k a)                      =>  Zero `k` a
  jam'   ::  Obj k a                                  =>  (a ⊕ a) `k` a
  (▾)    ::  forall a b c. (Obj k a,Obj k b, Obj k c) =>  (b `k` a) -> (c `k` a) -> (b ⊕ c) `k` a




---------------------------
-- Instances
----------------------------

instance Category (->) where
  type Obj (->) = Trivial
  (.) = (Prelude..)
  id = Prelude.id

instance Monoidal (->) where
  (f ⊗ g) (x `Pair` y) = (f x `Pair` g y)
  assoc ((x `Pair` y) `Pair` z) = (x `Pair` (y `Pair` z)) 
  assoc_ (x `Pair` (y `Pair` z)) = ((x `Pair` y) `Pair` z)  
  unitorR x = (x `Pair` Unit)
  unitorR_ (x `Pair` Unit) = x

instance Braided (->) where
  swap (x `Pair` y) = (y `Pair` x)

instance Monoidal' (->) where
  f ⊕ g = \case
    Inj1 x -> Inj1 (f x)
    Inj2 x -> Inj2 (g x)
  assoc' = \case
    Inj1 (Inj1 x) -> Inj1 x
    Inj1 (Inj2 x) -> Inj2 (Inj1 x)
    Inj2 x -> Inj2 (Inj2 x)
  assoc_' = \case
    (Inj1 x) -> (Inj1 (Inj1 x)) 
    (Inj2 (Inj1 x)) -> (Inj1 (Inj2 x)) 
    (Inj2 (Inj2 x)) -> (Inj2 x) 
  unitorR' x = Inj1 x
  unitorR_' = \case
    Inj1 x -> x
    Inj2 x -> case x of

instance Braided' (->) where
  swap' = \case
    Inj1 x -> Inj2 x
    Inj2 x -> Inj1 x
