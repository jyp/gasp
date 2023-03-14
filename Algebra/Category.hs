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

type TensorCon con = forall a b. (con a, con b) => con (a⊗b) :: Constraint
type LConTensor con = forall a b. con (a⊗b) => con a :: Constraint
type RConTensor con = forall a b. con (a⊗b) => con a :: Constraint

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


law_id_comp :: forall {k} (f :: k -> k -> Type) a b. (Category f, TestEqual (f a b), O2 f a b) => f a b -> Property
law_id_comp n = nameLaw "id/comp" (id . n =.= n)

forallMorphism :: forall {k} f {con :: k -> Constraint} x y.
                  (con ~ Obj f,
                   con x, con y,
                   forall α β. (con α, con β) => Arbitrary (f α β),
                   forall α β. (con α, con β) => Show (f α β),
                   ProdObj con, SumObj con)
               => Repr x -> Repr y -> (f x y -> Property) -> Property
forallMorphism t1 t2 = forAll (arbitrary2' t1 t2)

forallMorphism' :: forall {k} f {con :: k -> Constraint} .
                  (con ~ Obj f,
                   forall α β. (con α, con β) => Arbitrary (f α β),
                   forall α β. (con α, con β) => Show (f α β),
                   ProdObj con, SumObj con)
               => (forall x y. (con x, con y) => f x y -> Property) -> Property
forallMorphism' p = forallType @con (\t1 ->
                    forallType @con (\t2 ->
                    forallMorphism t1 t2 (\f ->
                    p f)))

law_comp_id :: forall {k} (f :: k -> k -> Type) a b. (Category f, TestEqual (f a b), O2 f a b) => f a b -> Property
law_comp_id n = nameLaw "comp/id" (n . id =.= n)

law_comp_assoc :: forall {k} (f :: k -> k -> Type) a b c d. (Category f, TestEqual (f a d), O4 f a b c d) => f c d -> f b c -> f a b -> Property
law_comp_assoc n m o = nameLaw "comp/assoc" (n . (m . o) =.= (n . m) . o)

law_comp_assoc' :: forall {k} (f :: k -> k -> Type) {con}.
  (forall x y. (con x, con y) => TestEqual (f x y),
   -- forall α β. (con α, con β) => Arbitrary (f α β),
   -- forall α β. (con α, con β) => Show (f α β),
   ProdObj con, SumObj con,
   con ~ Obj f, Category f) => Property
law_comp_assoc' = forallType @con (\t1 ->
                  forallType @con (\t2 ->
                  forallType @con (\t3 ->
                  forallType @con (\t4 ->
                  forallMorphism @f t1 t2 (\ h ->
                  forallMorphism @f t2 t3 (\ g ->
                  forallMorphism @f t3 t4 (\ f ->
                  f . (g . h) =.= (f . g) . h)))))))

laws_category :: forall {k} (f :: k -> k -> Type) {con}.
                 (forall x y. (con x, con y) => TestEqual (f x y),
   ProdObj con, SumObj con,
   con ~ Obj f, Category f)
              => Property
laws_category = product [forallMorphism' @f (\ f -> property (law_id_comp f))
                        ,forallMorphism' @f (\ f -> property (law_comp_id f))
                        ,law_comp_assoc' @f
                        ]


class Category cat => Dagger cat where
  dagger :: O2 cat a b => a `cat` b -> b `cat` a

(∘) :: forall {k} (cat :: k -> k -> Type) a b c con. (Category cat, con ~ Obj cat, con a, con b, con c) => cat b c -> cat a b -> cat a c
(∘) = (.) 


class ({-ProdObj (Obj cat), -}Category cat) => Monoidal (cat :: k -> k -> Type) where
  (⊗)      :: (Obj cat a, Obj cat b, Obj cat c, Obj cat d) => (a `cat` b) -> (c `cat` d) -> (a ⊗ c) `cat` (b ⊗ d)
  assoc    :: (Obj cat a, Obj cat b, Obj cat c) => ((a ⊗ b) ⊗ c) `cat` (a ⊗ (b ⊗ c))
  assoc_   :: (Obj cat a, Obj cat b, Obj cat c) => (a ⊗ (b ⊗ c)) `cat` ((a ⊗ b) ⊗ c)
  unitorR   :: (Obj cat a) => a `cat` (a ⊗ One)
  unitorR_  :: (Obj cat a) => (a ⊗ One) `cat` a
  unitorL   :: (Obj cat a, Obj cat One) => a `cat` (One ⊗ a)
  unitorL_  :: (Obj cat a, Obj cat One) => (One ⊗ a) `cat` a

  default unitorL :: forall a con. (con ~ Obj cat, con One, TensorCon con, Braided cat, Obj cat a) => a `cat` (One ⊗ a)
  unitorL = swap ∘ unitorR
     -- \\ objprod @(Obj cat) @a @One
     -- \\ objprod @(Obj cat) @One @a
     -- \\ objone @(Obj cat)

  default unitorL_ :: forall a con. (con ~ Obj cat, Braided cat, con One, TensorCon con, Obj cat a) => (One ⊗ a) `cat` a 
  unitorL_ = unitorR_ ∘ swap
     -- \\ objprod @(Obj cat) @a @One
     -- \\ objprod @(Obj cat) @One @a
     -- \\ objone @(Obj cat)


class Monoidal cat => Braided cat where
  swap     :: (Obj cat a, Obj cat b) => (a ⊗ b) `cat` (b ⊗ a)

class Braided cat => Symmetric cat

class Monoidal cat => Cartesian cat where
  exl   ::   forall a b. O2 cat a b                     =>    (a ⊗ b) `cat` a
  exr   ::   forall a b. O2 cat a b                     =>    (a ⊗ b) `cat` b
  dis   ::   forall a.  Obj cat a                       =>    a `cat` One
  dup   ::   forall a. Obj cat a                        =>    a `cat` (a ⊗ a)
  (▵)   ::   forall a b c. (Obj cat a,Obj cat b, Obj cat c) =>    (a `cat` b) -> (a `cat` c) -> a `cat` (b ⊗ c)

  {-# MINIMAL exl,exr,dup | exl,exr,(▵) | dis,dup | dis,(▵) #-}
  default dis :: forall a con. (con ~ Obj cat, con One, TensorCon con, Obj cat a) => a `cat` One
  dis = exr . unitorR
  default dup :: forall a con. (con ~ Obj cat, con One, TensorCon con, Obj cat a) => a `cat` (a⊗a)
  dup = id ▵ id
  default exl :: forall a b con. (con ~ Obj cat, con One, TensorCon con, con a, con b) =>  (a ⊗ b) `cat` a
  exl = unitorR_ . (id ⊗ dis)
  default exr :: forall a b con. (con ~ Obj cat, con One, TensorCon con, con a, con b) =>  (a ⊗ b) `cat` b
  exr = unitorL_ ∘ (dis ⊗ id)
  default (▵)   ::   forall a b c con. (con ~ Obj cat, con One, TensorCon con, Obj cat a,Obj cat b, Obj cat c) =>    (a `cat` b) -> (a `cat` c) -> a `cat` (b ⊗ c)
  f ▵ g = (f ⊗ g) ∘ dup 
  --         \\ objprod @(Obj k) @a @a
  --         \\ objprod @(Obj k) @b @c 

cartesianCross :: (Obj k (b1 ⊗ b2), Obj k b3, Obj k c, Obj k b1,
                     Obj k b2, Cartesian k) =>
                    k b1 b3 -> k b2 c -> k (b1 ⊗ b2) (b3 ⊗ c)
cartesianCross a b = (a . exl) ▵ (b . exr)


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
class Braided' cat => Symmetric' cat

type Cartesian' :: forall {k}. (k -> k -> Type) -> Constraint
class Monoidal' cat => Cartesian' cat where
  exl'  ::   forall a b. O2 cat a b                     =>    (a ⊕ b) `cat` a
  exr'  ::   forall a b. O2 cat a b                     =>    (a ⊕ b) `cat` b
  dis'  ::   forall a.   Obj cat a                      =>    a `cat` Zero
  dup'  ::   (Obj cat a)                   =>    a `cat` (a ⊕ a)
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
instance Symmetric (->)

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

instance Cartesian (->) where
  dup x = Pair x x
  exr (Pair _ x) = x
  exl (Pair x _) = x
  (f ▵ g) x = f x `Pair` g x
  dis _ = Unit

instance CoCartesian' (->) where
  inl' = Inj1
  inr' = Inj2
  new' = \case
  f ▾ g = \case
     Inj1 x -> f x
     Inj2 y -> g y
  jam' = \case
     Inj1 x -> x
     Inj2 x -> x
