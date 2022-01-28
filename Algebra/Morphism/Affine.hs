{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algebra.Morphism.Affine where

import Prelude (Eq(..), Ord(..), Functor(..), id,Bool(..))
import Algebra.Classes
import Algebra.Linear
import qualified Data.Map as M
import Data.Either
import Control.Applicative

import Algebra.Morphism.LinComb (LinComb(..))
import qualified Algebra.Morphism.LinComb as LC


data Affine x c = Affine c (LinComb x c)
  deriving (Functor, Eq, Ord)

instance Multiplicative c => Scalable c (Affine x c) where
  k *^ x = k *< x

instance (Ord x, AbelianAdditive c,DecidableZero c) => AbelianAdditive (Affine x c)
instance (Ord x, Group c,DecidableZero c) => Group (Affine x c) where
  negate = fmap negate
instance (Ord x, Additive c,DecidableZero c) => Additive (Affine x c) where
  (Affine c1 xs1) + (Affine c2 xs2) = Affine (c1 + c2) (xs1 + xs2)
  zero = Affine zero zero

splitVar :: Ord x => Additive c => x -> Affine x c -> (c, Affine x c)
splitVar x (Affine c0 (LinComb m)) = (M.findWithDefault zero x m, Affine c0 (LinComb (M.delete x m)))

-- | @solve x f@ solves the equation @f == 0@ for x.
-- Let f = k x + e.  If k == 0, return Left e. Otherwise, x and return Right -e/k. (The value of x)
solve :: Ord scalar => (Eq scalar, Division scalar, Group scalar, Ord x,DecidableZero scalar)
      => x -> Affine x scalar -> Either (Affine x scalar) (Bool,Affine x scalar)
solve x f = if k == zero then Left e else Right (k>zero,recip k *^ negate e) 
  where (k,e) = splitVar x f

-- | Constant affine expression
constant :: DecidableZero c => Ord x => c -> Affine x c
constant c = Affine c zero

var :: Multiplicative c => Additive c => v -> Affine v c
var x = Affine zero (LC.var x)

eval :: forall x c v. (Additive x, Scalable x x) => (c -> x) -> (v -> x) -> Affine v c -> x
eval fc fv (Affine c p) = fc c + LC.eval fc fv p

subst :: (Ord x, DecidableZero c, Multiplicative c) => (v -> Affine x c) -> Affine v c -> Affine x c
subst f (Affine c p) = constant c + LC.eval id f p 

mapVars :: Ord x => (v -> x) -> Affine v c -> Affine x c
mapVars f (Affine k e) = Affine k (LC.mapVars f e)

traverseVars :: Additive c => Ord x => Applicative f => (v -> f x) -> Affine v c -> f (Affine x c)
traverseVars f (Affine k e) = Affine k <$> LC.traverseVars f e
