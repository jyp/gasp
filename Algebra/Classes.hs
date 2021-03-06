{-# LANGUAGE TupleSections #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts, FlexibleInstances, DeriveGeneric #-}
module Algebra.Classes where

import Prelude (Int,Integer,Float,Double, (==), Monoid(..), Ord(..), Foldable,
                foldMap, Char,
                 Real(..), Enum(..), snd, Rational, Functor(..), Eq(..), Bool(..), Semigroup(..), Show(..), uncurry)

import qualified Prelude
import qualified Data.Ratio
import qualified Data.Map.Strict as M
import Data.Map (Map)
import Foreign.C
import Data.Word
import Data.Binary
import Data.Complex
import GHC.Generics
import Test.QuickCheck
import Control.Applicative

-- import Data.Functor.Utils ((#.))

infixl 6 -
infixl 6 +

infixl 7 *
infixr 7 *^
infixl 7 /
infixl 7 `mod`
infixl 7 `div`
infixr 8 ^
infixr 8 ^+

type Natural = Integer

newtype Sum a = Sum {fromSum :: a} deriving Generic

instance Binary a => Binary (Sum a)

instance Additive a => Monoid (Sum a) where
  mempty = Sum zero
  mappend = (<>)

instance Additive a => Semigroup (Sum a) where
  (<>) (Sum x) (Sum y) = Sum (x + y)

newtype Product a = Product {fromProduct :: a}

instance Multiplicative a => Semigroup (Product a) where
  (<>) (Product x) (Product y) = Product (x * y)

instance Multiplicative a => Monoid (Product a) where
  mempty = Product one
  mappend = (<>)

newtype Exponential a = Exponential {fromExponential :: a}

instance Additive a => Multiplicative (Exponential a) where
  Exponential a * Exponential b = Exponential (a + b)
  one = Exponential zero
  Exponential a ^+ n = Exponential (times n a)

instance Group a => Division (Exponential a) where
  recip (Exponential a) = Exponential (negate a)
  Exponential a / Exponential b = Exponential (a - b)

timesDefault :: (Additive a2, Prelude.Integral a1) => a1 -> a2 -> a2
timesDefault n0 = if n0 < 0 then Prelude.error "Algebra.Classes.times: negative number of times" else go n0
    where go 0 _ = zero
          go n x = if r == 0 then y + y else x + y + y
            where (m,r) = n `Prelude.divMod` 2
                  y = go m x

-- | Additive monoid
class Additive a where
  (+) :: a -> a -> a
  zero :: a
  times :: Natural -> a -> a
  times = timesDefault

class (Arbitrary a, Show a) => TestEqual a where
  (=.=) :: a -> a -> Property

infix 0 =.=

instance Multiplicative Property where
  one = property True
  (*) = (.&&.)

nameLaw :: Testable prop => Prelude.String -> prop -> Property
nameLaw x p = label x (counterexample x p)

law_zero_plus :: forall a. (Additive a, TestEqual a) => a -> Property
law_zero_plus n = nameLaw "zero/plus" (zero + n =.= n)

law_plus_zero :: (Additive a, TestEqual a) => a -> Property
law_plus_zero n = nameLaw "plus/zero" (n + zero =.= n)

law_plus_assoc :: (Additive a, TestEqual a) => a -> a -> a -> Property
law_plus_assoc m n o = nameLaw "plus/assoc" (n + (m + o) =.= (n + m) + o)

law_times :: (TestEqual a, Additive a) => Positive Integer -> a -> Property
law_times (Positive m) n = nameLaw "times" (times m n =.= timesDefault m n)

laws_additive :: forall a. (Additive a, TestEqual a) => Property
laws_additive = product [property (law_zero_plus @a)
                        ,property (law_plus_zero @a)
                        ,property (law_plus_assoc @a)
                        ,property (law_times @a)]

instance TestEqual Int where (=.=) = (===)


sum :: (Foldable t, Additive a) => t a -> a
sum xs = fromSum (foldMap Sum xs)

instance Additive Integer where
  (+) = (Prelude.+)
  zero = 0
  times n x = n * x

instance Additive Word32 where
  (+) = (Prelude.+)
  zero = 0
  times n x = Prelude.fromIntegral n * x

instance Additive Word16 where
  (+) = (Prelude.+)
  zero = 0
  times n x = Prelude.fromIntegral n * x

instance Additive Word8 where
  (+) = (Prelude.+)
  zero = 0
  times n x = Prelude.fromIntegral n * x

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

law_decidable_zero :: forall a. (DecidableZero a, TestEqual a) => Property
law_decidable_zero = property (isZero (zero @a))


instance DecidableZero Integer where
  isZero = (== 0)
instance DecidableZero CInt where
  isZero = (== 0)
instance DecidableZero Word32 where
  isZero = (== 0)
instance DecidableZero Word16 where
  isZero = (== 0)
instance DecidableZero Word8 where
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

law_plus_comm :: (TestEqual a, Additive a) => a -> a -> Property
law_plus_comm m n = nameLaw "plus/comm" (m + n =.= n + m)

laws_abelian_additive :: forall a. (Group a, TestEqual a) => Property
laws_abelian_additive = laws_additive @a .&&. product [property (law_plus_comm @a)]

instance AbelianAdditive Integer
instance AbelianAdditive CInt
instance AbelianAdditive Int
instance AbelianAdditive Double
instance AbelianAdditive Float
instance (Ord k,AbelianAdditive v) => AbelianAdditive (Map k v)

multDefault :: Group a => Natural -> a -> a
multDefault n x = if n < 0 then negate (times (negate n) x) else times n x

class Additive a => Group a where
  {-# MINIMAL (negate | (-) | subtract) #-}
  (-) :: a -> a -> a
  a - b = a + negate b
  subtract :: a -> a -> a
  subtract b a = a - b
  negate :: a -> a
  negate b = zero - b
  mult :: Integer -> a -> a
  mult = multDefault

law_negate_minus :: (TestEqual a, Group a) => a -> a -> Property
law_negate_minus m n = nameLaw "minus/negate" (m + negate n =.= m - n)

law_mult :: (TestEqual a, Group a) => Integer -> a -> Property
law_mult m n = nameLaw "mult" (mult m n =.= multDefault m n)


laws_group :: forall a. (Group a, TestEqual a) => Property
laws_group = laws_additive @a .&&. product [property (law_negate_minus @a)
                                           ,property (law_mult @a)]

laws_abelian_group :: forall a. (Group a, TestEqual a) => Property
laws_abelian_group = laws_group @a .&&. product [property (law_plus_comm @a)]

instance Group Integer where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance Group Int where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance Group CInt where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance Group Word32 where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance Group Word16 where
  (-) = (Prelude.-)
  negate = Prelude.negate

instance Group Word8 where
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
class (AbelianAdditive a, PreRing scalar) => Module scalar a where
  (*^) :: scalar -> a -> a

law_module_zero :: forall s a. (Module s a, TestEqual a) => s -> Property
law_module_zero s = nameLaw "module/zero" (s *^ zero =.= zero @a)

law_module_one :: forall s a. (Module s a, TestEqual a) => a -> Property
law_module_one x = nameLaw "module/one" ((one @s) *^ x =.= x)

law_module_sum :: forall s a. (Module s a, TestEqual a) => s -> a -> a -> Property
law_module_sum s x y = nameLaw "module/distr/left" (s *^ (x + y) =.= s*^x + s *^ y)

law_module_sum_left :: forall s a. (Module s a, TestEqual a) => s -> s -> a -> Property
law_module_sum_left s t x = nameLaw "module/distr/right" ((s + t) *^ x =.= s*^x + t *^ x)

law_module_mul :: forall s a. (Module s a, TestEqual a) => s -> s -> a -> Property
law_module_mul s t x = nameLaw "module/mul/assoc" ((s * t) *^ x =.= s *^ t *^ x)

laws_module :: forall s a. (Module s a, TestEqual a, Arbitrary s, Show s) => Property
laws_module = laws_additive @a .&&. product [property (law_module_zero @s @a)
                                            ,property (law_module_one @s @a)
                                            ,property (law_module_sum @s @a)
                                            ,property (law_module_sum_left @s @a)
                                            ,property (law_module_mul @s @a)
                                            ]

-- Comparision of maps with absence of a key equivalent to zero value.
instance (Ord x, Show x, Arbitrary x,TestEqual a,Additive a) => TestEqual (Map x a) where
  x =.= y = product (uncurry (=.=) <$> M.unionWith collapse ((,zero) <$> x) ((zero,) <$> y))
    where collapse :: (a,b) -> (c,d) -> (a,d)
          collapse (a,_) (_,b) = (a,b)


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

instance (Ord k, Module a b) => Module a (Map k b) where
  s *^ m = fmap (s *^) m

-- | Multiplicative monoid
class Multiplicative a where
  (*) :: a -> a -> a
  one :: a
  (^+) :: a -> Natural -> a

  x0 ^+ n0 = if n0 < 0 then Prelude.error "Algebra.Classes.^: negative exponent" else go x0 n0
    where go _ 0 = one
          go x n = if r == 0 then y * y else x * y * y
            where (m,r) = n `Prelude.divMod` 2
                  y = go x m


product :: (Multiplicative a, Foldable f) => f a -> a
product xs = fromProduct (foldMap Product xs)

instance Multiplicative Integer where
  (*) = (Prelude.*)
  one = 1
  (^+) = (Prelude.^)

instance Multiplicative CInt where
  (*) = (Prelude.*)
  one = 1
  (^+) = (Prelude.^)

instance Multiplicative Word32 where
  (*) = (Prelude.*)
  one = 1
  (^+) = (Prelude.^)

instance Multiplicative Word16 where
  (*) = (Prelude.*)
  one = 1
  (^+) = (Prelude.^)

instance Multiplicative Word8 where
  (*) = (Prelude.*)
  one = 1
  (^+) = (Prelude.^)

instance Multiplicative Int where
  (*) = (Prelude.*)
  one = 1
  (^+) = (Prelude.^)

instance Multiplicative Double where
  (*) = (Prelude.*)
  one = 1
  (^+) = (Prelude.^)

instance Multiplicative Float where
  (*) = (Prelude.*)
  one = 1
  (^+) = (Prelude.^)



type SemiRing a = (Multiplicative a, AbelianAdditive a)
type PreRing a = (SemiRing a, Group a)

fromIntegerDefault :: PreRing a => Integer -> a
fromIntegerDefault n = mult n one

class (Module a a, PreRing a) => Ring a where
  fromInteger :: Integer -> a
  fromInteger = fromIntegerDefault

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

  (^) :: a -> Integer -> a
  b ^ n | n < 0 = recip b ^+ negate n
        | True  = b ^+ n

instance Division Double where
  (/) = (Prelude./)
  recip = Prelude.recip
  (^) = (Prelude.^^)

instance Division Float where
  (/) = (Prelude./)
  recip = Prelude.recip
  (^) = (Prelude.^^)

class (Ring a, Division a) => Field a where
  fromRational :: Rational -> a
  fromRational x  =  fromInteger (Data.Ratio.numerator x) /
                     fromInteger (Data.Ratio.denominator x)

instance Field Double where
  fromRational = Prelude.fromRational

instance Field Float where
  fromRational = Prelude.fromRational


class Ring a => EuclideanDomain a where
    {-# MINIMAL (stdUnit | normalize) , (divMod | (div , mod)) #-}
    stdAssociate    :: a -> a
    stdUnit         :: a -> a
    normalize       :: a -> (a, a)

    div, mod        :: a -> a -> a
    divMod          :: a -> a -> (a,a)

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


gcd             :: (Integral a) => a -> a -> a
{-# NOINLINE [1] gcd #-}
gcd x y         =  gcd' (stdAssociate x) (stdAssociate y)
 where
   gcd'             :: (Eq a, Integral a) => a -> a -> a
   gcd' a 0  =  a
   gcd' a b  =  gcd' b (a `rem` b)

{- -}



--------------------------
-- Ratio instances
instance Prelude.Integral a => Additive (Data.Ratio.Ratio a) where
  zero = Prelude.fromInteger 0
  (+) = (Prelude.+)

instance Prelude.Integral a => AbelianAdditive (Data.Ratio.Ratio a) where

instance Prelude.Integral a => Group (Data.Ratio.Ratio a) where
  negate = Prelude.negate
  (-) = (Prelude.-)

instance Prelude.Integral a => Multiplicative (Data.Ratio.Ratio a) where
  one = Prelude.fromInteger 1
  (*) = (Prelude.*)
  (^+) = (Prelude.^)

instance Prelude.Integral a => Division (Data.Ratio.Ratio a) where
  recip = Prelude.recip
  (/) = (Prelude./)
  (^) = (Prelude.^^)
instance Prelude.Integral a => Module (Data.Ratio.Ratio a) (Data.Ratio.Ratio a) where
  (*^) = (*)
instance Prelude.Integral a => Ring (Data.Ratio.Ratio a) where
  fromInteger = Prelude.fromInteger
instance Prelude.Integral a => Field (Data.Ratio.Ratio a) where
  fromRational = Prelude.fromRational


----------------------
-- Complex instances
instance Module Rational Double where
    r *^ d = fromRational r * d
instance Additive a => Additive (Complex a) where
    (x:+y) + (x':+y')   =  (x+x') :+ (y+y')
    zero = zero :+ zero
instance Ring a => Multiplicative (Complex a) where
    (x:+y) * (x':+y')   =  (x*x'-y*y') :+ (x*y'+y*x')
    one = one :+ zero
instance Group a => Group  (Complex a) where
    (x:+y) - (x':+y')   =  (x-x') :+ (y-y')
    negate (x:+y)       =  negate x :+ negate y
instance AbelianAdditive a => AbelianAdditive (Complex a)
instance Ring a => Module (Complex a) (Complex a) where
  (*^) = (*)
instance Ring a => Module a (Complex a) where
  s *^ (x :+ y) =  (s *^ x :+ s *^ y)
instance Ring a => Ring (Complex a) where
    fromInteger n  =  fromInteger n :+ zero

instance  Field a => Division (Complex a)  where
    {-# SPECIALISE instance Division (Complex Double) #-}
    (x:+y) / (x':+y')   =  (x*x'+y*y') / d :+ (y*x'-x*y') / d
      where d   = x'*x' + y'*y'

instance Field a => Field (Complex a) where
    fromRational a =  fromRational a :+ zero

{-data Expr a where
  Embed :: a -> Expr a
  Add :: Expr a -> Expr a -> Expr a
  Mul :: Expr a -> Expr a -> Expr a
  Zero :: Expr a
  One :: Expr a
  deriving (Prelude.Show)


instance Additive (Expr a) where
  zero = Zero
  Zero + x = x
  x + Zero = x
  x + y = Add x y

instance Multiplicative (Expr a) where
  one = One
  One * x = x
  x * One = x
  x * y = Mul x y
-}

-- Syntax

ifThenElse :: Bool -> t -> t -> t
ifThenElse True a _ = a
ifThenElse False _ a = a



-- >>> times 5 (Embed "x")
-- Add (Add (Embed "x") (Add (Embed "x") (Embed "x"))) (Add (Embed "x") (Embed "x"))


-- >>> (Embed "x")
-- Zero


{-
Note: the following is not quite what we intuitively want, because

class Field a => AlgebraicallyClosed  a where
  sqrt :: a -> (a,a)

AlgebraicallyClosed numbers have two square roots.

-}

