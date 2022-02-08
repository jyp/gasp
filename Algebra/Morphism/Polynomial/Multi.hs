{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algebra.Morphism.Polynomial.Multi where

import Prelude ((&&), Bool(..), Int, Eq(..), Ord(..),Show(..), Functor(..), fromIntegral, id,(.),(||),Integer,Foldable(..),error)
import Data.List (intercalate,and,filter,zip)
import Data.Monoid
import Algebra.Classes
import Algebra.Morphism.Exponential
import qualified Algebra.Morphism.LinComb as LC
import Algebra.Morphism.LinComb (LinComb(..), fromLinComb)
import qualified Data.Map as M
import Data.Maybe (Maybe (..))
import Data.Traversable
import Control.Applicative
import Data.Function

-- | Monomial over an element set e, mapping each element to its
-- exponent
newtype Monomial e = M (Exp (LinComb e Int)) deriving (Multiplicative,Division,Ord,Eq,Show)

monoLinComb :: Monomial e -> LinComb e Int
monoLinComb (M (Exp x)) = x
-- Note: derived ordering is lexicographic.

mapMonoVars :: Ord e => (t -> e) -> Monomial t -> Monomial e
mapMonoVars f (M (Exp m)) = M (Exp (LC.mapVars f m)) 

traverseMonoVars :: (Applicative f, Ord e) => (v -> f e) -> Monomial v -> f (Monomial e)
traverseMonoVars f (M (Exp x)) = M . Exp <$> (LC.traverseVars f x)

monoDegree :: Monomial e -> Int
monoDegree =  LC.eval id (\_ -> 1) . monoLinComb
  -- LC.eval id (\_ -> Scalar 1) m

-- >>> monoDegree (varM "x" ^+3 * varM "y" ^+2)
-- 5

monoDivisible :: Ord k => Monomial k -> Monomial k -> Bool
monoDivisible (M (Exp (LinComb m))) (M (Exp (LinComb n))) =
  M.isSubmapOfBy (<=) n m


monoLcm :: Ord v => Monomial v -> Monomial v -> Monomial v
monoLcm (M (Exp (LinComb a))) (M (Exp (LinComb b)))
  = M $ Exp $ LinComb $ M.unionWith max a b

mapVars  :: Ord e => (t -> e) -> Polynomial t c -> Polynomial e c
mapVars f = P . LC.mapVars (mapMonoVars f) . fromPoly

-- | Map each monomial to its coefficient
newtype Polynomial e c = P (LC.LinComb (Monomial e) c)
  deriving (Additive,Group,AbelianAdditive,Functor,Foldable,Traversable,Eq,Ord,DecidableZero,Show)
deriving instance {-# Overlappable #-} Scalable s a => Scalable s (Polynomial k a)

fromPoly :: Polynomial e c -> LinComb (Monomial e) c
fromPoly (P x) = x
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

prodMonoPoly, (*!) :: (Ord e) => Monomial e -> Polynomial e c -> Polynomial e c
prodMonoPoly m (P p) = P (LC.mulVarsMonotonic m p)
(*!) = prodMonoPoly

-- This instance is incoherent, because there could be Scalable (Monomial e) c.
-- instance (Eq c, Ord c,Ring c, Ord e) => Scalable (Monomial e) (Polynomial e c) where
--   (*^) = prodMonoPoly

-------------------------------
-- Construction

varM :: e -> Monomial e
varM x = M (Exp (LC.var x))

-- >>> (varM "x" * varM "y" * varM "x" ^ 2)
-- M {fromM = Exp {fromExp = LinComb {fromLinComb = fromList [("x",3),("y",1)]}}}

varP :: Multiplicative c => e -> Polynomial e c
varP x = monoPoly (varM x)

-- >>> varP "x" + varP "y"
-- 1"x"+1"y"

-- >>> (varP "x" ^+ 2)
-- "x"^2

-- >>> ((varP "x" ^+ 2) * varP "y" + varP "y") * ((varP "x" ^+ 2) * varP "y" + varP "y")
-- 2"x"^2"y"^2+"x"^4"y"^2+"y"^2

data Term x c = Term c (Monomial x) deriving Show

termPoly :: Term x c -> Polynomial x c
termPoly (Term c m) = P (LinComb (M.singleton m c))

monoPoly :: Multiplicative c => Monomial e -> Polynomial e c
monoPoly m = P (LC.var m)

constPoly :: DecidableZero c => Additive c => Ord e => c -> Polynomial e c
constPoly c = P (LC.fromList [(one,c)])


-------------------------------
-- Evaluation

evalMono ::  Multiplicative x => (e -> x) -> Monomial e -> x
evalMono f (M (Exp m)) = fromLog (LC.eval @Integer fromIntegral (Log . f) m)

eval' :: (Multiplicative x, Additive x, Scalable c x) => (e -> x) -> Polynomial e c -> x
eval' = eval id

eval :: (Multiplicative x, Additive x, Scalable d x) => (c -> d) -> (v -> x) -> Polynomial v c -> x
eval fc fe (P p) = LC.eval fc (evalMono fe) p

-------------------------------
-- Substitution by evaluation

type Substitution e f c = e -> Polynomial f c

substMono :: DecidableZero c => Ord f => Ring c => Substitution e f c -> Monomial e -> Polynomial f c
substMono = evalMono

subst :: DecidableZero c => Ord f => Ord e => Ring c => Substitution e f c -> Polynomial e c -> Polynomial f c
subst = eval'

----------------------------
-- Traversing

bitraverse :: Ord w => Applicative f => (v -> f w) -> (c -> f d) -> Polynomial v c -> f (Polynomial w d)
bitraverse f g (P x) = P <$> LC.bitraverse (traverseMonoVars f) g x

-------------------------
-- Gröbner basis, division

instance (Field c, Ord x) => Multiplicative (Term x c) where
  one = Term one one
  Term x c * Term x' c' = Term (x*x') (c * c')
instance (Field c, Ord x) => Division (Term x c) where
  Term x c / Term x' c' = Term (x/x') (c / c')
leadingView :: Polynomial v c -> Maybe (Term v c,Polynomial v c)
leadingView (P (LinComb a)) = flip fmap (M.minViewWithKey a) $ \
  ((x,c),xs) -> (Term c x, P (LinComb xs))

prepareDivisor :: Polynomial x c -> (Term x c, Polynomial x c)
prepareDivisor p = case leadingView p of
  Nothing -> error "multivariate division by zero"
  Just x -> x

-- Division by a several polynomials. Returns quotients and remainders
division :: DecidableZero c => Field c => Ord x => Polynomial x c -> [Polynomial x c]
         -> ([(Int,Term x c)] ,  Polynomial x c) 
division p0 fi0 = go p0 [] zero where
  fi = fmap prepareDivisor fi0
  go p qi r = case leadingView p of
    Nothing -> (qi,r)
    Just (ltp@(Term _ lmp),pRest) ->
      case [ iMatch
           | iMatch@(_,(Term _ fm,_)) <- zip [0..] fi,
             lmp `monoDivisible` fm] of
        [] -> go pRest qi (r + termPoly ltp)
        ((i,(ltf,frest)):_) -> go (pRest - (q *!! frest)) ((i,q):qi) r
          where q = (ltp/ltf)

-- >>> varP "x" ^+ 3 - varP "y" ^+ 3
-- P (LinComb (fromList [(M (Exp (LinComb (fromList [("x",3)]))),1),(M (Exp (LinComb (fromList [("y",3)]))),-1)]))

-- >>> leadingView (varP "x" ^+ 3 - varP "y" ^+ 3)
-- Just (Term 1 (M (Exp (LinComb (fromList [("x",3)])))),P (LinComb (fromList [(M (Exp (LinComb (fromList [("y",3)]))),-1)])))

-- >>> division (varP "x" ^+ 3 - varP "y" ^+ 3) [varP "x" - varP "y"]
-- ([(0,Term 1.0 (M (Exp (LinComb (fromList [("x",0),("y",2)]))))),(0,Term 1.0 (M (Exp (LinComb (fromList [("x",1),("y",1)]))))),(0,Term 1.0 (M (Exp (LinComb (fromList [("x",2)])))))],P (LinComb (fromList [])))

(*!!)  :: (Field c, Ord x) => Term x c -> Polynomial x c -> Polynomial x c
Term c m *!! p = m `prodMonoPoly` (c *^ p) 

-- | Subtract the right amount of g from f so that the leading terms cancel.
-- p85 in Ideals, Varieties and Algorithms
spoly :: (DecidableZero c, Field c, Ord x) =>
           (Term x c, Polynomial x c)
           -> (Term x c, Polynomial x c) -> Polynomial x c
spoly (ltf@(Term _ m),f) (ltg@(Term _ n),g)
  = (xγ / ltf) *!! f - (xγ / ltg) *!! g where xγ = Term one (monoLcm m n) 
-- note that the leading terms are guaranteed to cancel, so they are
-- not even used in the result expression. (This way we can work with
-- approximations and the algorithm still works)



nfWrt :: Eq c => DecidableZero c => Field c => Ord x => Polynomial x c -> [Polynomial x c] -> Polynomial x c 
nfWrt p fi0 = go p where
  fi = fmap prepareDivisor fi0
  go h = case leadingView h of
    Nothing -> zero
    Just h'@(Term _ lmh,_) ->
      case filter (\(Term _ fm,_) -> lmh `monoDivisible` fm) fi of
        [] -> h
        (g:_) -> go (spoly h' g)

