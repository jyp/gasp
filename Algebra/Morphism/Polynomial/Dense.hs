{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
module Algebra.Morphism.Polynomial.Dense (Polynomial, fromPoly, degree, var) where

import Prelude (Int,  Eq(..), Ord(..),Show(..), Functor(..), (.),  Maybe(..),error,otherwise,Double)
import Data.Monoid
import Algebra.Linear
import Algebra.Classes
import Data.Sequence as S

-- Invariant: 1st element not zero.
data Polynomial c = P {fromPoly :: S.Seq c} deriving (Functor,Show)

fromCoefs :: (Additive c, Eq c) => Seq c -> Polynomial c
fromCoefs = P . S.dropWhileL (== zero)


zipWithLonger :: (Additive a1, Additive a2) => (a1 -> a2 -> c) -> Seq a1 -> Seq a2 -> Seq c
zipWithLonger f a b = zipWith f (S.replicate (n-S.length a) zero <> a)
                                (S.replicate (n-S.length b) zero <> b)
  where n = max (S.length a) (S.length b)

plus :: Additive a => Seq a -> Seq a -> Seq a
plus = zipWithLonger (+)

instance (Additive a, Eq a) => Additive (Polynomial a) where
  P a + P b  = fromCoefs (zipWithLonger (+) a b)
  zero  = P Empty


instance (Eq a,Group a) => Group (Polynomial a) where
  negate = fmap negate

instance (Eq a, AbelianAdditive a) => AbelianAdditive (Polynomial a)

instance Ring a => Multiplicative (Polynomial a) where
  one = P (S.singleton one)
  P x * P y = P (mul x y)

mul :: Ring a => Seq a -> Seq a -> Seq a
mul Empty _ = Empty
mul _ Empty = Empty
mul (a :|> a0) bb0@(b :|> b0) = ((a0 *< b) `plus` (bb0 `mul` a)) |> (a0*b0) 
     -- note swapping the operands in the recursive call, so that we
     -- advance towards the end of the list on both sides after two
     -- recursive calls.

var :: Ring a => Polynomial a
var = P (S.fromList [one,zero])

instance (Ring a, Eq a) => Scalable (Polynomial a) (Polynomial a) where
  (*^) = (*)
instance (Ring a, Eq a) => Ring (Polynomial a)
  
degree :: Polynomial c -> Maybe Int
degree (P x) = if l == 0 then Nothing else Just (l-1)
  where l = S.length x
  
divide :: Field a => Seq a -> Seq a -> Seq a
divide a d | S.length d == 0 = error "dense polynomial division by zero"
           | S.length a < S.length d = Empty
           | otherwise = divide' nsteps a (d <> S.replicate nsteps zero)
           where nsteps = S.length a - S.length d

divide' :: Field a => Int -> Seq a -> Seq a -> Seq a
divide' n _ _ | n < 0 = S.Empty
divide' n (an :<| ar) d@(dm :<| dr) =
  q <| divide' (n-1) (S.zipWith (-) ar (q *< dr)) (sinit d)
  where q = an / dm
        sinit (x :|> _) = x
        sinit _ = error "module Algebra.Structure.Polynomial.Dense: sinit: panic"
divide' _ _ _ = error "module Algebra.Structure.Polynomial.Dense: divide': panic"


instance Field a => Division (Polynomial a) where
  P q / P d = P (divide q d)

-- >>> (var + one) * (var - one) :: Polynomial Int
-- P {fromPoly = fromList [1,0,-1]}

-- >>> (var ^+ 2 - one) / (var + one) :: Polynomial Double
-- P {fromPoly = fromList [1.0,-1.0]}
