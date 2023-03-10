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
  assoc'   :: (Obj cat a, Obj cat b, Obj cat c) => (a ⊗ (b ⊗ c)) `cat` ((a ⊗ b) ⊗ c)
  unitorR   :: (Obj cat a) => a `cat` (a ⊗ One)
  unitorR'  :: (Obj cat a) => (a ⊗ One) `cat` a
  unitorL   :: (Obj cat a, Obj cat One) => a `cat` (One ⊗ a)
  unitorL'  :: (Obj cat a, Obj cat One) => (One ⊗ a) `cat` a

  default unitorL :: forall a. (SMC cat, Obj cat a) => a `cat` (One ⊗ a)
  unitorL = swap ∘ unitorR
     \\ objprod @(Obj cat) @a @One
     \\ objprod @(Obj cat) @One @a
     \\ objunit @(Obj cat)


class Monoidal cat => SMC cat where
  swap     :: (Obj cat a, Obj cat b) => (a ⊗ b) `cat` (b ⊗ a)

class Monoidal k => Cartesian k where
  exl   ::  {-<-} forall a b. O2 k a b                     => {->-}   (a ⊗ b) `k` a
  exr   ::  {-<-} forall a b. O2 k a b                     => {->-}   (a ⊗ b) `k` b
  dis   ::  {-<-} forall a.  Obj k a                      => {->-}   a `k` One
  dup   ::  {-<-} forall a. Obj k a                   => {->-}   a `k` (a ⊗ a)
  (▵)   ::  {-<-} forall a b c. (Obj k a,Obj k b, Obj k c) => {->-}   (a `k` b) -> (a `k` c) -> a `k` (b ⊗ c)

  {-# MINIMAL exl,exr,dup | exl,exr,(▵) | dis,dup | dis,(▵) #-}
  dis = disDefault
  dup = id ▵ id
  exl = exlDefault
  exr = exrDefault
  (▵) = (▵!)

type TensorCon con = forall a b. (con a, con b) => con (a⊗b) :: Constraint
type LConTensor con = forall a b. con (a⊗b) => con a :: Constraint
type RConTensor con = forall a b. con (a⊗b) => con a :: Constraint


disDefault :: forall k a. (Cartesian k, Obj k a ) =>  a `k` One
disDefault = exr . unitorR
     \\ objprod @(Obj k) @a @One
     \\ objunit @(Obj k)

exlDefault :: forall k con a b. (con ~ Obj k, Cartesian k, O2 k a b) =>  (a ⊗ b) `k` a
exlDefault = unitorR' . (id ⊗ dis)
          \\ objprod @(Obj k) @a @b
          \\ objprod @(Obj k) @a @One
          \\ objunit @(Obj k)

exrDefault :: forall k con a b. (con ~ Obj k,Cartesian k, O2 k a b) =>  (a ⊗ b) `k` b
exrDefault = unitorL' ∘ (dis ⊗ id)
          \\ objprod @(Obj k) @a @b
          \\ objprod @(Obj k) @One @b
          \\ objunit @(Obj k)


(▵!) :: forall k con a b c . (con ~ Obj k,Cartesian k,O3 k a b c) =>   (a `k` b) -> (a `k` c) -> a `k` (b ⊗ c)
f ▵! g = (f ⊗ g) ∘ dup 
          \\ objprod @(Obj k) @a @a
          \\ objprod @(Obj k) @b @c 




---------------------------
-- Instances
----------------------------

instance Category (->) where
  type Obj (->) = Trivial
  (.) = (Prelude..)
  id = Prelude.id


