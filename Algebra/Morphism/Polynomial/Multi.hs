{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algebra.Morphism.Polynomial.Multi where

import Prelude (Int, Eq(..), Ord(..),Show(..), Functor(..), fromIntegral, all,id,not,(.),(||))
import Data.List (intercalate,and)
import Data.Monoid
import Algebra.Linear
import Algebra.Classes
import Algebra.Morphism.Exponential
import Data.Map (Map)
import qualified Data.Map as M
import Data.Function (on)
import Data.Maybe (Maybe (..))

-- | Monomial over an element set e, mapping each element to its
-- exponent
newtype Monomial e = M (Exponential (Map e Int)) deriving (Multiplicative,Division,Ord,Eq)


mapMonoVars :: Ord e => (t -> e) -> Monomial t -> Monomial e
mapMonoVars f (M (Exponential m)) = M (Exponential (M.fromList [(f x, e) | (x,e) <- M.assocs m]))


-- | Map each monomial to its coefficient
newtype Polynomial e c = P {fromPoly :: (Map (Monomial e) c)} deriving (Additive,Group,AbelianAdditive,Functor)

instance (Eq e, Eq c, Additive c) => Eq (Polynomial e c) where
   (==) = (==) `on` (M.filter (/= zero) . fromPoly)

instance (Ord e, Ord c, Additive c) => Ord (Polynomial e c) where
   compare = compare `on` (M.filter (/= zero) . fromPoly)

instance (Ring c, Ord e) => Multiplicative (Polynomial e c) where
  one = P (M.singleton one one)
  P p * P q = P (M.fromListWith (+) [(m1 * m2, coef1 * coef2) | (m1,coef1) <- M.toList p, (m2,coef2) <- M.toList q])

instance (DecidableZero c, Ord e) => DecidableZero (Polynomial e c) where
  isZero (P p) = all isZero (M.elems p) 

isConstant :: (Eq c, Ord e, Additive c) => Polynomial e c -> Maybe c
isConstant (P p) = if and [m == one || c == zero | (m,c) <- M.assocs p] then
                     Just (M.findWithDefault zero one p) else Nothing

instance (Ring c, Ord e) => Scalable (Polynomial e c) (Polynomial e c) where
  (*^) = (*)

instance (Ring c,Ord e) => Ring (Polynomial e c)

instance (Ring c, Ord e) => Scalable c (Polynomial e c) where
  (*^) = (*<)


prodMonoPoly :: (Ord e) => Monomial e -> Polynomial e c -> Polynomial e c
prodMonoPoly m (P p) = P (M.mapKeys (* m) p)

-- causes overlapping instances (a bit annoying)
-- instance (Eq c, Ord c,Ring c, Ord e) => Scalable (Monomial e) (Polynomial e c) where
--   (*^) = prodMonoPoly
  
instance Show e => Show (Monomial e) where
  show (M (Exponential xs)) = mconcat ([show m <> (if coef /= 1 then ("^" <> show coef) else mempty)| (m,coef) <- M.toList xs]) 
  
instance (Show c, Show e, Eq c, Multiplicative c) => Show (Polynomial e c) where
  show (P xs) = intercalate "+" ([(if coef /= one then show coef else mempty) <> show m  | (m,coef) <- M.toList xs])


-------------------------------
-- Construction

varM :: e -> Monomial e
varM x = M (Exponential (M.singleton x one))

-- >>> (varM "x" * varM "y" * varM "x" ^ 2)
-- "x"^3"y"

varP :: Multiplicative c => e -> Polynomial e c
varP x = monoPoly (varM x)

-- >>> varP "x" + varP "y"
-- 1"x"+1"y"

-- >>> (varP "x" ^+ 2)
-- "x"^2

-- >>> ((varP "x" ^+ 2) * varP "y" + varP "y") * ((varP "x" ^+ 2) * varP "y" + varP "y")
-- 2"x"^2"y"^2+"x"^4"y"^2+"y"^2

monoPoly :: Multiplicative c => Monomial e -> Polynomial e c
monoPoly m = P (M.singleton m one)

constPoly :: Ord e => Multiplicative c => c -> Polynomial e c
constPoly c = P (M.singleton one c)



-------------------------------
-- Evaluation

evalMono ::  Multiplicative x => (e -> x) -> Monomial e -> x
evalMono f (M (Exponential m)) = product [ f v ^+ fromIntegral e | (v, e) <- M.assocs m ] 

eval' :: (Multiplicative x, Additive x, Scalable c x) => (e -> x) -> Polynomial e c -> x
eval' = eval id

eval :: (Multiplicative x, Additive x, Scalable d x) => (c -> d) -> (e -> x) -> Polynomial e c -> x
eval fc fe (P p) = sum [ fc c *^ evalMono fe m | (m, c) <- M.assocs p ] 

-------------------------------
-- Substitution by evaluation

type Substitution e f c = e -> Polynomial f c

substMono :: Ord f => Ring c => Substitution e f c -> Monomial e -> Polynomial f c
substMono = evalMono

subst :: Ord f => Ord e => Ring c => Substitution e f c -> Polynomial e c -> Polynomial f c
subst = eval'
