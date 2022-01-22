{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
module Algebra.Structure.Polynomial.Dense where

import Prelude (Int, String, Eq(..), Ord(..),Show(..), Functor(..), (.), Float, Maybe(..),error)
import Data.List (replicate,length,scanr)
import Data.Monoid
import Algebra.Linear
import Algebra.Classes
import Data.Map (Map)
import qualified Data.Map as M
import Control.Applicative
import Data.Sequence as S

data Polynomial c = P {fromPoly :: S.Seq c} deriving (Functor,Show)

fromCoefs :: (Additive c, Eq c) => Seq c -> Polynomial c
fromCoefs = P . S.dropWhileL (== zero)


zipWithLonger :: (Additive a1, Additive a2) => (a1 -> a2 -> c) -> Seq a1 -> Seq a2 -> Seq c
zipWithLonger f a b = zipWith f (S.replicate (n-S.length a) zero <> a)
                                (S.replicate (n-S.length b) zero <> b)
  where n = max (S.length a) (S.length b)

plus :: Additive a => Seq a -> Seq a -> Seq a
plus = zipWithLonger (+)

minus :: Group a => Seq a -> Seq a -> Seq a
minus = zipWithLonger (-)

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

instance (Ring a, Eq a) => Module (Polynomial a) (Polynomial a) where
  (*^) = (*)
instance (Ring a, Eq a) => Ring (Polynomial a)
  
degree :: Polynomial c -> Maybe Int
degree (P x) = if l == 0 then Nothing else Just (l-1)
  where l = S.length x
  
divide :: Field a => Seq a -> Seq a -> Seq a
divide a d | S.length d == 0 = error "polynomial division by zero"
            | S.length a < S.length d = S.Empty
divide ana@(an :<| a) d@(dm :<| _) = q <| (S.drop 1 (ana `minus` (q *< d)) `divide` d)
            where q = an / dm

instance Field a => Division (Polynomial a) where
  P q / P d = P (divide q d)

-- >>> (var ^+ 2 ) / var
-- <interactive>:2422:2-18: warning: [-Wtype-defaults]
--     • Defaulting the following constraints to type ‘ghc-prim-0.6.1:GHC.Types.Double’
--         (Show a0)
--           arising from a use of ‘System.IO.print’ at <interactive>:2422:2-18
--         (Field a0) arising from a use of ‘it’ at <interactive>:2422:2-18
--     • In a stmt of an interactive GHCi command: System.IO.print it
-- P {fromPoly = fromList [1.0,-1.0]}
