module Algebra.Structure.Ratio where

import Algebra.Classes
import Prelude (Ord(..), Eq(..),Integer,Enum(..),Show(..),Ordering(..), error, otherwise, (.), Int, ($))
import Text.Show (showParen, showString)
------------------------------------------------------------------------
-- Divide by zero and arithmetic overflow
------------------------------------------------------------------------

-- We put them here because they are needed relatively early
-- in the libraries before the Exception type has been defined yet.

{-# NOINLINE divZeroError #-}
divZeroError :: a
divZeroError = error "division by zero"

{-# NOINLINE ratioZeroDenominatorError #-}
ratioZeroDenominatorError :: a
ratioZeroDenominatorError = error "ratioZeroDenomException"

{-# NOINLINE overflowError #-}
overflowError :: a
overflowError = error "overflowException"

{-# NOINLINE underflowError #-}
underflowError :: a
underflowError = error "underflowException"


data  Ratio a = !a :% !a  deriving Eq -- ^ @since 2.01

type Rational = Ratio Integer

--------------------------------------------------------------
-- Instances for @Ratio@
--------------------------------------------------------------

-- | @since 2.0.1
instance  (Integral a)  => Ord (Ratio a)  where
    {-# SPECIALIZE instance Ord Rational #-}
    (x:%y) <= (x':%y')  =  x * y' <= x' * y
    (x:%y) <  (x':%y')  =  x * y' <  x' * y

-- | @since 2.0.1
instance  Ring a  => Additive (Ratio a)  where
  zero = zero :% one
  (x:%y) + (x':%y')   =  reduce (x*y' + x'*y) (y*y')

instance Multiplicative (Ratio a) where
  one = one :% one
  (x:%y) * (x':%y')   =  reduce (x * x') (y * y')

instance Group (Ratio a) where
    (x:%y) - (x':%y')   =  reduce (x*y' - x'*y) (y*y')
    negate (x:%y)       =  (negate x) :% y

    -- abs (x:%y)          =  abs x :% y
    -- signum (x:%_)       =  signum x :% 1
    -- fromInteger x       =  fromInteger x :% 1

-- | @since 2.0.1
instance  (Integral a)  => Division (Ratio a)  where
    {-# SPECIALIZE instance Division Rational #-}
    (x:%y) / (x':%y')   =  (x*y') % (y*x')
    recip (0:%_)        = ratioZeroDenominatorError
    recip (x:%y)
        | x < 0         = negate y :% negate x
        | otherwise     = y :% x

instance Integral a => Field (Ratio a) where
    -- fromRational (x:%y) =  fromInteger x % fromInteger y

-- | @since 2.0.1
-- instance  (Integral a)  => Real (Ratio a)  where
--     {-# SPECIALIZE instance Real Rational #-}
--     toRational (x:%y)   =  toInteger x :% toInteger y

-- -- | @since 2.0.1
-- instance  (Integral a)  => RealFrac (Ratio a)  where
--     {-# SPECIALIZE instance RealFrac Rational #-}
--     properFraction (x:%y) = (fromInteger (toInteger q), r:%y)
--                           where (q,r) = quotRem x y
--     round r =
--       let
--         (n, f) = properFraction r
--         x = if r < 0 then -1 else 1
--       in
--         case (compare (abs f) 0.5, odd n) of
--           (LT, _) -> n
--           (EQ, False) -> n
--           (EQ, True) -> n + x
--           (GT, _) -> n + x

-- | @since 2.0.1
instance  (Show a)  => Show (Ratio a)  where
    {-# SPECIALIZE instance Show Rational #-}
    showsPrec p (x:%y)  =  showParen (p > ratioPrec) $
                           showsPrec ratioPrec1 x .
                           showString " % " .
                           showsPrec ratioPrec1 y

-- | @since 2.0.1
instance  (Integral a)  => Enum (Ratio a)  where
    {-# SPECIALIZE instance Enum Rational #-}
    succ x              =  x + 1
    pred x              =  x - 1

    -- toEnum n            =  fromIntegral n :% 1
    -- fromEnum            =  fromInteger . truncate

    -- enumFrom            =  numericEnumFrom
    -- enumFromThen        =  numericEnumFromThen
    -- enumFromTo          =  numericEnumFromTo
    -- enumFromThenTo      =  numericEnumFromThenTo


-- | 'reduce' is a subsidiary function used only in this module.
-- It normalises a ratio by dividing both numerator and denominator by
-- their greatest common divisor.
reduce ::  (Integral a) => a -> a -> Ratio a
{-# SPECIALISE reduce :: Integer -> Integer -> Rational #-}
reduce _ 0              =  ratioZeroDenominatorError
reduce x y              =  (x `quot` d) :% (y `quot` d)
                           where d = gcd x y

(%) :: a -> a -> Ratio a
x % y                   =  reduce (x * signum y) (abs y)

ratioPrec, ratioPrec1 :: Int
ratioPrec  = 7  -- Precedence of ':%' constructor
ratioPrec1 = ratioPrec + 1
