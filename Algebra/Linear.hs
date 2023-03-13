{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
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

import Algebra.Classes
import Prelude (Show(..),Eq(..),($),Ord,error,flip)
import Control.Applicative
import Data.Foldable hiding (sum,product)
import Data.Traversable
import Control.Monad.State
import Algebra.Category
import Algebra.Types
import Data.Constraint
import Algebra.Category.Relation
import Data.Functor.Rep
import Data.Distributive

type VectorSpace scalar a = (Field scalar, Module scalar a, Group a)
-- Because of the existence of bases, vector spaces can always be made representable (Traversable, Applicative) functors.
-- So we'd be better off using the following definition:

-- | Representation of vector as traversable functor
class (Finite (Rep v),Representable v, Foldable v, Applicative v) => VectorR v where
  vectorSplit :: (v ~ (f ⊗ g)) => Dict (VectorR f, VectorR g)
  vectorSplit = error "vectorSplit: not product type"
  vectorCut :: (v ~ (f ⊕ g)) => Dict (VectorR f, VectorR g)
  vectorCut = error "vectorCut: not sum type"

instance (VectorR v, VectorR w) => VectorR (v ⊗ w) where
  vectorSplit = Dict

instance (VectorR v, VectorR w) => VectorR (v ⊕ w) where
  vectorCut = Dict

instance (VectorR One)
instance (VectorR Zero)

instance SumObj VectorR where
  objsum = Dict
  objleftright = vectorCut
  objzero = Dict

instance ProdObj VectorR where
  objprod = Dict
  objfstsnd = vectorSplit
  objunit = Dict

-- ... but this is missing the link with *^ for module.  We should be
-- able to add forall s. PreRing s => Module s (v s), but this creates
-- problems when defining instances.

class VectorR v => InnerProdSpace v where
  inner :: Field s => v s -> v s -> s

--------------------------------------------------------------
-- Construction of finite vectors

type VZero x = Zero x

data VNext v a = VNext {vnextInit :: !(v a), vnextLast :: !a} deriving (Functor,Foldable,Traversable,Show,Eq,Ord)

instance Distributive v => Distributive (VNext v) where
  collect f x = VNext (collect (vnextInit . f) x) (vnextLast . f <$> x)
instance Representable a => Representable (VNext a) where
  type Rep (VNext a) = One ⊕ (Rep a)
  index (VNext xs x) = \case
    Inj1 _ -> x
    Inj2 i -> index xs i
  tabulate f = VNext (tabulate (f . Inj2)) (f (Inj1 Unit))
instance VectorR a => VectorR (VNext a) where

data V f a where
  V0 :: V Zero a
  (:/) :: !(V f a) -> !a -> V (VNext f) a

deriving instance Functor (V f)
deriving instance Foldable (V f)
deriving instance Traversable (V f)
deriving instance Show a => Show (V f a)
deriving instance Eq a => Eq (V f a)

class (Foldable f,Applicative f) => IsVec f where
  reifyVec :: f a -> V f a

instance IsVec Zero where
  reifyVec FunctorZero = V0

instance IsVec f => IsVec (VNext f) where
  reifyVec (VNext xs x) = reifyVec xs :/ x

fromV :: V f a -> f a
fromV V0 = FunctorZero
fromV (xs :/ x) = VNext (fromV xs) x

instance IsVec f => Applicative (V f) where
  pure x = reifyVec (pure x)
  fs <*> xs = reifyVec (fromV fs <*> fromV xs)

instance Applicative v => Applicative (VNext v) where
  pure x = VNext (pure x) x
  VNext fs f <*> VNext xs x = VNext (fs <*> xs) (f x)


type V1' = VNext Zero
type V2' = VNext V1'
type V3' = VNext V2'

pattern V1' :: a -> V1' a
pattern V1' x = VNext FunctorZero x
pattern V2' :: forall a. a -> a -> V2' a
pattern V2' x y = VNext (V1' x) y
pattern V3' :: forall a. a -> a -> a -> V3' a
pattern V3' x y z = VNext (V2' x y) z

--------------------------------------------
-- Euclidean spaces with a (inner product)

-- | Make a Euclidean vector out of a traversable functor. (The p)
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
instance (Functor f, Scalable s a) => Scalable s (Euclid f a) where
  s *^ Euclid t = Euclid (((s*^) <$>) t)

pureMat :: (Applicative v, Applicative w) => s -> Mat s v w
pureMat x = Mat (pure (pure x))

instance (Applicative f,Applicative g,Additive a) => Additive (Mat a f g) where
  zero = pureMat zero
  x + y = matFlat ((+) <$> flatMat x <*> flatMat y)
instance (Applicative f,Applicative g,AbelianAdditive a) => AbelianAdditive (Mat a f g) where
instance (Applicative f,Applicative g,Group a) => Group (Mat a f g) where
  negate x = matFlat (negate <$> flatMat x)
  x - y = matFlat ((-) <$> flatMat x <*> flatMat y)

instance (Functor f, Functor g,Scalable s a) => Scalable s (Mat a f g) where
  s *^ Mat t = Mat (((s*^) <$>) <$> t)

-- | Hadamard product
(⊙) :: Applicative v => Multiplicative s => v s -> v s -> v s
x ⊙ y = (*) <$> x <*> y

instance Distributive f => Distributive (Euclid f) where
  collect f = Euclid . collect (fromEuclid . f)
instance Representable f => Representable (Euclid f) where
  type Rep (Euclid f) = Rep f
  index (Euclid x) = index x
  tabulate f = Euclid (tabulate f)
instance VectorR f => VectorR (Euclid f)
instance (VectorR f) => InnerProdSpace (Euclid f) where
  inner x y = sum (x ⊙ y) -- fixme

(·) :: Field s => InnerProdSpace v => v s -> v s -> s
(·) = inner

sqNorm :: Field s => InnerProdSpace v => v s -> s
sqNorm x = inner x x

norm :: Algebraic s => InnerProdSpace v => v s  -> s
norm = sqrt . sqNorm

normalize :: (VectorSpace s (v s)) => Algebraic s => InnerProdSpace v => v s -> v s
normalize v = recip (norm v) *^ v

-- | Cross product in 3 dimensions https://en.wikipedia.org/wiki/Cross_product
(×) :: Ring a => V3 a -> V3 a -> V3 a
(V3 a1 a2 a3) × (V3 b1 b2 b3) = V3 (a2*b3 - a3*b2)  (negate (a1*b3 - a3*b1)) (a1*b2 - a2*b1)

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


instance Ring s => Category (Mat s) where
  type Obj (Mat s) = VectorR
  (.) = matMul
  id = fromRel id

fromRel :: (VectorR a, VectorR b) => Rel s (Rep a) (Rep b) -> Mat s a b
fromRel (Rel f) = Mat (tabulate (\i -> tabulate (\j -> f i j)))
  
instance Ring s => Monoidal (Mat s) where
  assoc = fromRel assoc
  assoc_ = fromRel assoc_
  unitorR = fromRel unitorR
  unitorR_ = fromRel unitorR_
  Mat f ⊗ Mat g = Mat (Comp (fmap (\x -> fmap Comp  (fmap (\y -> liftA2 (liftA2 (*)) (fmap pure x) (pure y)) g)) f))


instance Ring s => Braided (Mat s) where
  swap = fromRel swap

instance Ring s => Monoidal' (Mat s) where
  assoc' = fromRel assoc'
  assoc_' = fromRel assoc_'
  unitorR' = fromRel unitorR'
  unitorR_' = fromRel unitorR_'
  Mat f ⊕ Mat g = Mat (FunctorProd
                        ((flip FunctorProd (pure zero)) <$> f)
                        (FunctorProd (pure zero) <$> g))

instance Ring s => Cartesian' (Mat s) where
  Mat f ▴ Mat g = Mat (FunctorProd <$> f <*> g)
  dis' = fromRel dis'

instance Ring s => Braided' (Mat s) where
  swap' = fromRel swap'

instance Ring s => CoCartesian' (Mat s) where
  inl' = fromRel inl'
  inr' = fromRel inr'
  new' = fromRel new'
  jam' = fromRel jam'
  Mat f ▾ Mat g = Mat (FunctorProd f g)
  
type Mat3x3 s = SqMat V3 s
type Mat2x2 s = SqMat V2 s

pattern Mat2x2 :: forall s. s -> s -> s -> s -> Mat s V2 V2
pattern Mat2x2 a b c d = Mat (V2 (V2 a c)
                                 (V2 b d))

pattern Mat3x3 :: forall s. s -> s -> s -> s -> s -> s -> s -> s -> s -> Mat s V3 V3
pattern Mat3x3 a b c d e f g h i = Mat (V3 (V3 a d g)
                                           (V3 b e h)
                                           (V3 c f i))


rotation2d :: Transcendental a => a -> Mat2x2 a
rotation2d θ = transpose $ Mat $ V2 (V2 (cos θ) (-sin θ))
                                    (V2 (sin θ)  (cos θ))

-- >>> rotation2d (pi/2)
-- Mat {fromMat = V2' (V2' 6.123233995736766e-17 (-1.0)) (V2' 1.0 6.123233995736766e-17)}


crossProductMatrix :: Group a => V3 a -> Mat3x3 a
crossProductMatrix (V3 a1 a2 a3) = Mat3x3 zero  (-a3) a2
                                          a3    zero  (-a1)
                                          (-a2) a1    zero

outerWith :: (Applicative v, Applicative w)
           => (s -> t -> u) -> w s -> v t -> Mat u v w
outerWith f v1 v2 = matFlat (f <$> Flat (pure v1) <*> Flat (pure <$> v2))


-- | Outer product 
outer :: (Applicative v, Applicative w, Multiplicative s)
    => Euclid w s -> Euclid v s -> Mat s (Euclid w) (Euclid v)
v1 `outer` v2 = outerWith (*) v2 v1


diagonal :: Eq (Rep v) => Representable v => Ring s => Applicative v => v s -> SqMat v s
diagonal v = outerWith (\x (y,a) -> if x == y then a else zero) (tabulate id) ((,) <$> (tabulate id) <*> v)

-- | 3d rotation around given axis
rotation3d :: Transcendental a => a -> V3 a -> Mat3x3 a
rotation3d θ u = cos θ *^ id +
                 sin θ *^ crossProductMatrix u +
                 (1 - cos θ) *^ (u `outer` u)


-- | 3d rotation mapping the direction of 'from' to that of 'to'
rotationFromTo :: forall a. (Algebraic a)
               => V3 a -> V3 a -> Mat3x3 a
rotationFromTo from to = c *^ id + s *^ crossProductMatrix v + (1-c) *^ (v `outer` v)
  where y = to
        x = from
        v :: V3 a
        v = x × y -- axis of rotation
        c = inner x y -- cos of angle
        s = norm v -- sin of angle

-- >>> let u = (V3 (1::Double) 0 0); v = (V3 0 1 1); in (rotationFromTo u v) `matVecMul` u
-- Euclid {fromEuclid = VNext (VNext (VNext VZero 0.0) 1.4142135623730951) 1.4142135623730951}

-- | Transposition as distribution
transpose :: Functor f => Distributive g => Mat a f g -> Mat a g f
transpose = Mat . distribute . fromMat

instance Ring s => Dagger (Mat s) where
  dagger = transpose

matMul :: (Foldable u, Ring s, Applicative w, Applicative v, Applicative u) => Mat s u w -> Mat s v u -> Mat s v w
matMul a (Mat b) = Mat (matVecMul a <$> b)


(<+>) :: (Applicative f, Additive b) => f b -> f b -> f b
u <+> v = (+) <$> u <*> v

matVecMul :: forall s v w. (Ring s, Foldable v,Applicative v,Applicative w) => Mat s v w -> v s -> w s
matVecMul (Mat m) x = foldr (<+>) (pure zero) ((*<) <$> x <*> m)

-- >>> let t1 = rotation2d (1::Double) in matMul (transpose t1) t1
-- Mat {fromMat = VNext (VNext VZero (VNext (VNext VZero 1.0) 0.0)) (VNext (VNext VZero 0.0) 1.0)}
prop_laws :: Property
prop_laws = product [laws_testEqual @(BernsteinP V2' Double)
                    ,laws_ring @(BernsteinP V2' Double)]


return []
runTests :: IO Bool
runTests = $quickCheckAll
