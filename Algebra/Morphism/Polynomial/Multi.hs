{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algebra.Morphism.Polynomial.Multi where

import Prelude (Int, Eq(..), Ord(..),Show(..), Functor(..), fromIntegral, id,(.),(||),Integer)
import Data.List (intercalate,and)
import Data.Monoid
import Algebra.Classes
import Algebra.Morphism.Exponential
import qualified Algebra.Morphism.LinComb as LC
import Algebra.Morphism.LinComb (LinComb(..))
import qualified Data.Map as M
import Data.Maybe (Maybe (..))

-- | Monomial over an element set e, mapping each element to its
-- exponent
newtype Monomial e = M (Exponential (LinComb e Int)) deriving (Multiplicative,Division,Ord,Eq)

mapMonoVars :: Ord e => (t -> e) -> Monomial t -> Monomial e
mapMonoVars f (M (Exponential m)) = M (Exponential (LC.mapVars f m)) 

-- | Map each monomial to its coefficient
newtype Polynomial e c = P {fromPoly :: LC.LinComb (Monomial e) c}
  deriving (Additive,Group,AbelianAdditive,Functor,Eq,Ord,DecidableZero,Show)

instance (Ring c, DecidableZero c, Ord e) => Multiplicative (Polynomial e c) where
  one = P (LC.var one)
  P p * P q = P (LC.fromList [(m1 * m2, coef1 * coef2) | (m1,coef1) <- LC.toList p, (m2,coef2) <- LC.toList q])

isConstant :: (Eq c, Ord e, Additive c) => Polynomial e c -> Maybe c
isConstant (P p) = if and [m == one || c == zero | (m,c) <- LC.toList p] then
                     Just (M.findWithDefault zero one (fromLinComb p)) else Nothing

instance (DecidableZero c, Ring c, Ord e) => Scalable (Polynomial e c) (Polynomial e c) where
  (*^) = (*)

instance (DecidableZero c,Ring c,Ord e) => Ring (Polynomial e c) where
  fromInteger = constPoly . fromInteger

deriving instance (Ord x, Scalable c c) => Scalable c (Polynomial x c)

prodMonoPoly :: (Ord e) => Monomial e -> Polynomial e c -> Polynomial e c
prodMonoPoly m (P p) = P (LC.mapVars (* m) p)

-- causes overlapping instances (a bit annoying)
-- instance (Eq c, Ord c,Ring c, Ord e) => Scalable (Monomial e) (Polynomial e c) where
--   (*^) = prodMonoPoly
  
instance Show e => Show (Monomial e) where
  show (M (Exponential xs)) = mconcat ([show m <> (if coef /= 1 then ("^" <> show coef) else mempty)| (m,coef) <- LC.toList xs]) 

-------------------------------
-- Construction

varM :: e -> Monomial e
varM x = M (Exponential (LC.var x))

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
monoPoly m = P (LC.var m)

constPoly :: DecidableZero c => Additive c => Ord e => c -> Polynomial e c
constPoly c = P (LC.fromList [(one,c)])


-------------------------------
-- Evaluation

evalMono ::  Multiplicative x => (e -> x) -> Monomial e -> x
evalMono f (M (Exponential m)) = fromLogarithm (LC.eval @Integer fromIntegral (Logarithm . f) m)

eval' :: (Multiplicative x, Additive x, Scalable c x) => (e -> x) -> Polynomial e c -> x
eval' = eval id

eval :: (Multiplicative x, Additive x, Scalable d x) => (c -> d) -> (e -> x) -> Polynomial e c -> x
eval fc fe (P p) = LC.eval fc (evalMono fe) p

-------------------------------
-- Substitution by evaluation

type Substitution e f c = e -> Polynomial f c

substMono :: DecidableZero c => Ord f => Ring c => Substitution e f c -> Monomial e -> Polynomial f c
substMono = evalMono

subst :: DecidableZero c => Ord f => Ord e => Ring c => Substitution e f c -> Polynomial e c -> Polynomial f c
subst = eval'
