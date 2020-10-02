{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RebindableSyntax #-}

module Algebra.Linear where

import Algebra.Classes hiding ((*<))
import Prelude (cos,sin,Floating(..),Functor(..),Show(..),Eq(..),Int,fst,($),Ord,Double)
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Control.Monad.State
import Algebra.Category
data VZero a = VZero deriving (Functor,Foldable,Traversable,Show,Eq,Ord)
instance Applicative VZero where
  pure _ = VZero
  VZero <*> VZero = VZero

data VNext v a = VNext !(v a) !a deriving (Functor,Foldable,Traversable,Show,Eq,Ord)
instance Applicative v => Applicative (VNext v) where
  pure x = VNext (pure x) x
  VNext fs f <*> VNext xs x = VNext (fs <*> xs) (f x)


type V1' = VNext VZero
type V2' = VNext V1'
type V3' = VNext V2'

pattern V1' :: a -> V1' a
pattern V1' x = VNext VZero x
pattern V2' :: forall a. a -> a -> V2' a
pattern V2' x y = VNext (V1' x) y
pattern V3' :: forall a. a -> a -> a -> V3' a
pattern V3' x y z = VNext (V2' x y) z

-- | Make a Euclidean vector out of a traversable functor
newtype Euclid f a = Euclid {fromEuclid :: f a} deriving (Functor,Foldable,Traversable,Show,Eq,Ord,Applicative)

type V3 = Euclid V3'
type V2 = Euclid V2'

pattern V2 :: forall a. a -> a -> Euclid V2' a
pattern V2 x y = Euclid (V2' x y)
pattern V3 :: forall a. a -> a -> a -> Euclid V3' a
pattern V3 x y z = Euclid (V3' x y z)

instance (Applicative f,Additive a) => Additive (Euclid f a) where
  zero = pure zero
  x + y =  (+) <$> x <*> y
instance (Applicative f,AbelianAdditive a) => AbelianAdditive (Euclid f a) where
instance (Applicative f,Group a) => Group (Euclid f a) where
  negate x = negate <$> x
  x - y = (-) <$> x <*> y

instance (Applicative f,Module s a) => Module s (Euclid f a) where
  s *^ t = (s*^) <$> t

pureMat :: (Applicative v, Applicative w) => s -> Mat s v w
pureMat x = Mat (pure (pure x))

instance (Applicative f,Applicative g,Additive a) => Additive (Mat a f g) where
  zero = pureMat zero
  x + y = matFlat ((+) <$> flatMat x <*> flatMat y)
instance (Applicative f,Applicative g,AbelianAdditive a) => AbelianAdditive (Mat a f g) where
instance (Applicative f,Applicative g,Group a) => Group (Mat a f g) where
  negate x = matFlat (negate <$> flatMat x)
  x - y = matFlat ((-) <$> flatMat x <*> flatMat y)

instance (Applicative f, Applicative g,Module s a) => Module s (Mat a f g) where
  s *^ Mat t = Mat (((s*^) <$>) <$> t)

-- Would be nice: (forall s. Field s => VectorSpace s (v s)) =>
-- But appears to be buggy (GHC 8.6)
class VectorR v => InnerProdSpace v where
  inner :: Field s => v s -> v s -> s

-- | Hadamard product
(⊙) :: Applicative v => Multiplicative s => v s -> v s -> v s
x ⊙ y = (*) <$> x <*> y

instance (VectorR f) => InnerProdSpace (Euclid f) where
  inner x y = add (x ⊙ y)

(·) :: Field s => InnerProdSpace v => v s -> v s -> s
(·) = inner

sqNorm :: Field s => InnerProdSpace v => v s -> s
sqNorm x = inner x x

norm :: Field s => InnerProdSpace v => Floating s => v s  -> s
norm = sqrt . sqNorm

normalize :: (VectorSpace s (v s)) => Floating s => InnerProdSpace v => v s -> v s
normalize v = recip (norm v) *^ v

-- | Cross product in 3 dimensions https://en.wikipedia.org/wiki/Cross_product
(×) :: Ring a => V3 a -> V3 a -> V3 a
(V3 a1 a2 a3) × (V3 b1 b2 b3) = V3 (a2*b3 - a3*b2)  (negate (a1*b3 - a3*b1)) (a1*b2 - a2*b1)

index :: Applicative v => Traversable v => v Int
index = fst (runState (sequenceA (pure increment)) zero)
  where increment = do x <- get; put (x+1); return x

type SqMat v s = Mat s v v

-- | Matrix type. (w s) is a column. (v s) is a row.
newtype Mat s w v = Mat {fromMat :: w (v s)} deriving Show

-- | View of the matrix as a composition of functors.
newtype Flat w v s = Flat {fromFlat :: w (v s)} deriving (Show,Functor,Foldable)
flatMat :: Mat s w v -> Flat w v s
flatMat (Mat x) = (Flat x)
matFlat :: Flat w v s -> Mat s w v
matFlat (Flat x) = (Mat x)

instance (Applicative w, Applicative v) => Applicative (Flat w v) where
  pure x = Flat (pure (pure x))
  Flat f <*> Flat a = Flat (((<*>) <$> f) <*> a)

-- | Representation of vector as traversable functor
type VectorR v = (Applicative v,Traversable v)
  -- Fixme: we should be able to use forall s. PreRing s => Module s (v s), but GHC does not like it.

instance Ring s => Category (Mat s) where
  type Con v = VectorR v
  (.) = matMul
  id = identity

type Mat3x3 s = SqMat V3 s
type Mat2x2 s = SqMat V2 s

pattern Mat2x2 :: forall s. s -> s -> s -> s -> Mat s V2 V2
pattern Mat2x2 a b c d = Mat (V2 (V2 a c)
                                 (V2 b d))

pattern Mat3x3 :: forall s. s -> s -> s -> s -> s -> s -> s -> s -> s -> Mat s V3 V3
pattern Mat3x3 a b c d e f g h i = Mat (V3 (V3 a d g)
                                           (V3 b e h)
                                           (V3 c f i))

infixr 7 *<
-- Law:
-- (*<) = (*^)
(*<) :: (Functor f, Multiplicative b) => b -> f b -> f b
s *< v = (s*) <$> v


(<+>) :: (Applicative f, Additive b) => f b -> f b -> f b
u <+> v = (+) <$> u <*> v


matVecMul :: forall s v w. (Ring s, Foldable v,Applicative v,Applicative w) => Mat s v w -> v s -> w s
matVecMul (Mat m) x = foldr (<+>) (pure zero) ((*<) <$> x <*> m) -- If GHC gets fixed: use VectorR constraint instead of Applicative, and add instead of foldr.

rotation2d :: (Group a,Floating a) => a -> Mat2x2 a
rotation2d θ = transpose $ Mat $ V2 (V2 (cos θ) (-sin θ))
                                    (V2 (sin θ)  (cos θ))

-- >>> rotation2d (pi/2)
-- Mat {fromMat = V2' (V2' 6.123233995736766e-17 (-1.0)) (V2' 1.0 6.123233995736766e-17)}

crossProductMatrix :: Group a => V3 a -> Mat3x3 a
crossProductMatrix (V3 a1 a2 a3) = Mat3x3 zero  (-a3) a2
                                          a3    zero  (-a1)
                                          (-a2) a1    zero

-- | Tensor product
(⊗) :: (Applicative v, Applicative w, Multiplicative s)
    => w s -> v s -> Mat s w v
v1 ⊗ v2 = tensorWith (*) v2 v1

tensorWith :: (Applicative v, Applicative w)
           => (s -> t -> u) -> w s -> v t -> Mat u v w
tensorWith f v1 v2 = matFlat (f <$> Flat (pure v1) <*> Flat (pure <$> v2))

identity :: Traversable v => Ring s => Applicative v => SqMat v s
identity = tensorWith (\x y -> if x == y then one else zero) index index

diagonal :: Traversable v => Ring s => Applicative v => v s -> SqMat v s
diagonal v = tensorWith (\x (y,a) -> if x == y then a else zero) index ((,) <$> index <*> v)

-- | 3d rotation around given axis
rotation3d :: Ring a => Floating a => a -> V3 a -> Mat3x3 a
rotation3d θ u = cos θ *^ identity +
                 sin θ *^ crossProductMatrix u +
                 (1 - cos θ) *^ (u ⊗ u)

-- | 3d rotation mapping the direction of 'from' to that of 'to'
rotationFromTo :: (Floating a, Module a a,Field a)
               => V3 a -> V3 a -> Mat3x3 a
rotationFromTo from to = c *^ identity + s *^ crossProductMatrix v + (1-c) *^ (v ⊗ v)
  where y = to
        x = from
        v = x × y -- axis of rotation
        c = inner x y -- cos of angle
        s = norm v -- sin of angle

-- >>> let u = (V3 (1::Double) 0 0); v = (V3 0 1 1); in (rotationFromTo u v) `matVecMul` u
-- Euclid {fromEuclid = VNext (VNext (VNext VZero 0.0) 1.4142135623730951) 1.4142135623730951}

transpose :: Applicative g => Traversable f => Mat a f g -> Mat a g f
transpose = Mat . sequenceA . fromMat

matMul :: (Traversable u, Ring s, Applicative w, Applicative v, Applicative u) => Mat s u w -> Mat s v u -> Mat s v w
matMul a (Mat b) = Mat (matVecMul a <$> b)


-- >>> let t1 = rotation2d (1::Double) in matMul (transpose t1) t1
-- Mat {fromMat = VNext (VNext VZero (VNext (VNext VZero 1.0) 0.0)) (VNext (VNext VZero 0.0) 1.0)}



-- The group of Orthogonal matrices, using "Multiplicative" for respecting conventions a bit better
newtype OrthoMat v s = OrthoMat (SqMat v s)

instance (Ring s, Applicative v, Traversable v) => Multiplicative (OrthoMat v s) where
  one = OrthoMat id
  OrthoMat m * OrthoMat n = OrthoMat (m . n)

instance (Ring s, Applicative v, Traversable v) => Division (OrthoMat v s) where
  recip (OrthoMat m) = OrthoMat (transpose m)


