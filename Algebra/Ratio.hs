{-# LANGUAGE MultiParamTypeClasses #-}
module Algebra.Ratio where

import Prelude (Integer, error, Eq(..), Bool(..))
import Algebra.Classes

data Ratio a = !a :% !a  deriving (Eq)
type MyRational = Ratio Integer

-- | 'reduce' is a subsidiary function used only in this module.
-- It normalises a ratio by dividing both numerator and denominator by
-- their greatest common divisor.
reduce :: (Integral a) => a -> a -> Ratio a
{-# SPECIALISE reduce :: Integer -> Integer -> MyRational #-}
reduce x y
  | y == 0 =  Prelude.error "reduce: division by zero"
  | True      =  (x `quot` d) :% (y `quot` d)
                           where d = gcd x y

(%) :: (Integral a) => a -> a -> Ratio a
x % y                   =  reduce (x * stdUnit y) (stdAssociate y)


instance Integral a => AbelianAdditive (Ratio a) where

instance (Integral a) => Additive (Ratio a) where
    (x:%y) + (x':%y')   =  reduce (x*y' + x'*y) (y*y')
    zero = zero :% one
    times n (x :% y) = reduce (times n x) y

instance (Integral a) => Multiplicative (Ratio a) where
    (x:%y) * (x':%y')   =  reduce (x * x') (y * y')
    one = 1 :% 1

instance Integral a => Group (Ratio a) where
    (x:%y) - (x':%y')   =  reduce (x*y' - x'*y) (y*y')
    negate (x:%y)       =  (-x) :% y

instance Integral a => Module (Ratio a) (Ratio a) where
  (*^) = (*)

instance Integral a => Ring (Ratio a) where
    fromInteger x       =  fromInteger x :% 1

instance Integral a => Division (Ratio a) where
  recip (x:%y) = y:%x

instance Integral a => Field (Ratio a) where


{- -}
