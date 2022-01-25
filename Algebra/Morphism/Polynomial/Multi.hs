{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algebra.Morphism.Polynomial.Multi where

import Prelude (Int, String, Eq(..), Ord(..),Show(..), Functor(..), (.), Float)
import Data.List (intercalate)
import Data.Monoid
import Algebra.Linear
import Algebra.Classes
import Data.Map (Map)
import qualified Data.Map as M
import Control.Applicative

-- | Monomial over an element set e, mapping each element to its
-- exponent
newtype Monomial e = M (Exponential (Map e Int)) deriving (Multiplicative,Division,Ord,Eq)

-- | Map each monomial to its coefficient
newtype Polynomial e c = P (Map (Monomial e) c) deriving (Additive,Group,AbelianAdditive,Functor)

instance (Eq c, Ord c,Ring c, Ord e) => Multiplicative (Polynomial e c) where
  one = P (M.singleton one one)
  P p * P q = P (M.fromListWith (+) [(m1 * m2, coef1 * coef2) | (m1,coef1) <- M.toList p, (m2,coef2) <- M.toList q])

instance (Eq c, Ord c,Ring c, Ord e) => Module (Polynomial e c) (Polynomial e c) where
  (*^) = (*)

instance (Eq c, Ord c,Ring c,Ord e) => Ring (Polynomial e c)

instance (Eq c, Ord c,Ring c, Ord e) => Module c (Polynomial e c) where
  (*^) = (*<)

prodMonoPoly :: (Ord e) => Monomial e -> Polynomial e c -> Polynomial e c
prodMonoPoly m (P p) = P (M.mapKeys (* m) p)

showExp :: Int -> String
showExp n  = c <$> show n
  where
    c '0' = '⁰'
    c '1' = '¹'
    c '2' = '²'
    c '3' = '³'
    c '4' = '⁴'
    c '5' = '⁵'
    c '6' = '⁶'
    c '7' = '⁷'
    c '8' = '⁸'
    c '9' = '⁹'
    c x = x

  
instance Show e => Show (Monomial e) where
  show (M (Exponential xs)) = mconcat ([show m <> (if coef /= 1 then ("^" <> show coef) else mempty)| (m,coef) <- M.toList xs]) 
  
instance (Show c, Show e, Eq c, Multiplicative c) => Show (Polynomial e c) where
  show (P xs) = intercalate "+" ([(if coef /= one then show coef else mempty) <> show m  | (m,coef) <- M.toList xs])

varM :: e -> Monomial e
varM x = M (Exponential (M.singleton x one))

-- >>> (varM "x" * varM "y" * varM "x" ^ 2)
-- "x"^3"y"

varP :: Multiplicative c => e -> Polynomial e c
varP x = P (M.singleton (varM x) one)

-- >>> varP "x" + varP "y"
-- 1"x"+1"y"

-- >>> (varP "x" ^+ 2)
-- "x"^2

-- >>> ((varP "x" ^+ 2) * varP "y" + varP "y") * ((varP "x" ^+ 2) * varP "y" + varP "y")
-- 2"x"^2"y"^2+"x"^4"y"^2+"y"^2
