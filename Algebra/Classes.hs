{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts, FlexibleInstances #-}
module Algebra.Classes where

import Prelude as Algebra.Classes (Int,Integer,Float,Double, Foldable (..), (==), Monoid(..), Ord(..)
                                  ,Real(..), Enum(..), snd, Rational, Functor(..), error, Eq(..), Bool(..))
import qualified Prelude
import qualified Data.Ratio
import qualified Data.Map.Strict as M
import Data.Map (Map)
import Foreign.C

infixl 6 -
infixl 6 +

infixl 7 *
infixr 7 *^
infixl 7 /
infixl 7 `mod`
infixl 7 `div`

type Natural = Integer

newtype Sum a = Sum {fromSum :: a}

instance Additive a => Monoid (Sum a) where
  mempty = Sum zero
  mappend (Sum x) (Sum y) = Sum (x + y)

newtype Product a = Product {fromProduct :: a}

instance Multiplicative a => Monoid (Product a) where
  mempty = Product one
  mappend (Product x) (Product y) = Product (x * y)

newtype Exponential a = Exponential {fromExponential :: a}

instance Additive a => Multiplicative (Exponential a) where
  Exponential a * Exponential b = Exponential (a + b)
  one = Exponential zero
  Exponential a ^ n = Exponential (times n a)

instance Group a => Division (Exponential a) where
  recip (Exponential a) = Exponential (negate a)
  Exponential a / Exponential b = Exponential (a - b)

-- | Additive monoid
class Additive a where
  (+) :: a -> a -> a
  zero :: a
  times :: Natural -> a -> a
  times 0 _ = zero
  times n x = if r == 0 then y + y else x + y + y
    where (m,r) = n `Prelude.divMod` 2
          y = times m x

add :: (Foldable t, Additive a) => t a -> a
add xs = fromSum (foldMap Sum xs)

instance Additive Integer where
  (+) = (Prelude.+)
  zero = 0
  times n x = n * x

instance Additive CInt where
  (+) = (Prelude.+)
  zero = 0
  times n x = Prelude.fromIntegral n * x

instance Additive Int where
  (+) = (Prelude.+)
  zero = 0
  times n x = Prelude.fromIntegral n * x

instance Additive Double where
  (+) = (Prelude.+)
  zero = 0
  times n x = Prelude.fromIntegral n * x

instance Additive Float where
  (+) = (Prelude.+)
  zero = 0
  times n x = Prelude.fromIntegral n * x

instance (Ord k,Additive v) => Additive (Map k v) where
  (+) = M.unionWith (+)
  zero = M.empty
  times n = fmap (times n)

class Additive r => DecidableZero r where
  isZero :: r -> Bool

instance DecidableZero Integer where
  isZero = (== 0)
instance DecidableZero CInt where
  isZero = (== 0)
instance DecidableZero Int where
  isZero = (== 0)
instance DecidableZero Double where
  isZero = (== 0)
instance DecidableZero Float where
  isZero = (== 0)
instance (Ord k,DecidableZero v) => DecidableZero (Map k v) where
  isZero = Prelude.all isZero

class Additive a => AbelianAdditive a
  -- just a law.
instance AbelianAdditive Integer
instance AbelianAdditive CInt
instance AbelianAdditive Int
instance AbelianAdditive Double
instance AbelianAdditive Float
instance (Ord k,AbelianAdditive v) => AbelianAdditive (Map k v)

class Additive a => Group a where
  {-# MINIMAL (negate | (-)) #-}
  (-) :: a -> a -> a
  a - b = a + negate b
  negate :: a -> a
  negate b = zero - b
  mult :: Integer -> a -> a
  mult n x = if n < 0 then negate (times n (negate x)) else times n x

instance Group Integer where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance Group Int where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance Group CInt where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance Group Double where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance Group Float where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance (Ord k,Group v) => Group (Map k v) where
  -- This definition does not work:
  -- (-) = M.unionWith (-)
  -- because if a key is not present on the lhs. then the rhs won't be negated.
  negate = fmap negate

-- | Module
class (AbelianAdditive a, Ring scalar) => Module scalar a where
  (*^) :: scalar -> a -> a

instance Module Integer Integer where
  (*^) = (*)

instance Module Int Int where
  (*^) = (*)

instance Module CInt CInt where
  (*^) = (*)

instance Module Double Double where
  (*^) = (*)

instance Module Float Float where
  (*^) = (*)

instance (Ord k,Ring v) => Module v (Map k v) where
  s *^ m = fmap (s *) m

-- | Multiplicative monoid
class Multiplicative a where
  (*) :: a -> a -> a
  one :: a
  (^) :: a -> Natural -> a

  (^) _ 0 = one
  (^) x n = if r == 0 then y * y else x * y * y
    where (m,r) = n `Prelude.divMod` 2
          y = (^) y m

multiply :: (Multiplicative a, Foldable f) => f a -> a
multiply xs = fromProduct (foldMap Product xs)

instance Multiplicative Integer where
  (*) = (Prelude.*)
  one = 1
  (^) = (Prelude.^)

instance Multiplicative CInt where
  (*) = (Prelude.*)
  one = 1
  (^) = (Prelude.^)

instance Multiplicative Int where
  (*) = (Prelude.*)
  one = 1
  (^) = (Prelude.^)

instance Multiplicative Double where
  (*) = (Prelude.*)
  one = 1
  (^) = (Prelude.^)

instance Multiplicative Float where
  (*) = (Prelude.*)
  one = 1
  (^) = (Prelude.^)

type SemiRing a = (Multiplicative a, AbelianAdditive a)

class (SemiRing a, Group a) => Ring a where
  fromInteger :: Integer -> a
  fromInteger n = mult n one

instance Ring Integer where
  fromInteger = Prelude.fromInteger

instance Ring CInt where
  fromInteger = Prelude.fromInteger

instance Ring Int where
  fromInteger = Prelude.fromInteger

instance Ring Double where
  fromInteger = Prelude.fromInteger

instance Ring Float where
  fromInteger = Prelude.fromInteger

class Multiplicative a => Division a where
  {-# MINIMAL (recip | (/)) #-}
  recip :: a -> a
  recip x         =  one / x

  (/) :: a -> a -> a
  x / y           =  x * recip y

instance Division Double where
  (/) = (Prelude./)

instance Division Float where
  (/) = (Prelude./)

class (Ring a, Division a) => Field a where
  fromRational :: Rational -> a
  fromRational x  =  fromInteger (Data.Ratio.numerator x) /
                     fromInteger (Data.Ratio.denominator x)

instance Field Double where
  fromRational = Prelude.fromRational

instance Field Float where
  fromRational = Prelude.fromRational

type VectorSpace scalar a = (Field scalar, Module scalar a)

class Ring a => EuclideanDomain a where
    stdAssociate    :: a -> a
    stdUnit         :: a -> a
    normalize       :: a -> (a, a)

    div, mod        :: a -> a -> a
    divMod          :: a -> a -> (a,a)

    -- Minimal complete definition:
    --      (stdUnit or normalize) and (divMod or (div and mod))
    stdAssociate x  =  x `div` stdUnit x
    stdUnit x       =  snd (normalize x)
    normalize x     =  (stdAssociate x, stdUnit x)

    n `divMod` d    =  (n `div` d, n `mod` d)
    n `div` d       =  q  where (q,_) = divMod n d
    n `mod` d       =  r  where (_,r) = divMod n d


instance  EuclideanDomain Integer  where
    div             =  Prelude.div
    mod             =  Prelude.mod
    stdAssociate x  =  Prelude.abs x
    stdUnit x       =  if x < 0 then -1 else 1

instance  EuclideanDomain CInt  where
    div             =  Prelude.div
    mod             =  Prelude.mod
    stdAssociate x  =  Prelude.abs x
    stdUnit x       =  if x < 0 then -1 else 1

instance  EuclideanDomain Int  where
    div             =  Prelude.div
    mod             =  Prelude.mod
    stdAssociate x  =  Prelude.abs x
    stdUnit x       =  if x < 0 then -1 else 1

class (Real a, Enum a, EuclideanDomain a) => Integral a  where
    quot, rem       :: a -> a -> a
    quotRem         :: a -> a -> (a,a)
    toInteger       :: a -> Integer

    n `quot` d      =  q  where (q,_) = quotRem n d
    n `rem` d       =  r  where (_,r) = quotRem n d
    quotRem n d     =  if Prelude.signum r == - Prelude.signum d then (q+one, r-d) else qr
      where qr@(q,r) = divMod n d

instance  Integral Integer  where
    quot      =  Prelude.quot
    rem       =  Prelude.rem
    toInteger = Prelude.toInteger

{-
Note: the following is not quite what we intuitively want, because

class Field a => AlgebraicallyClosed  a where
  sqrt :: a -> (a,a)

AlgebraicallyClosed numbers have two square roots.

-}
