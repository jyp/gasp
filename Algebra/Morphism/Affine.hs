{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algebra.Morphism.Affine where

import Prelude (Eq(..), Ord(..), Functor(..), id)
import Algebra.Classes
import Algebra.Linear
import qualified Data.Map as M
import Data.Either

import Algebra.Morphism.LinComb  hiding (eval)
import qualified Algebra.Morphism.LinComb as LC


data Affine x c = Affine c (LinComb x c)
  deriving (Functor, Eq, Ord)

instance Multiplicative c => Scalable c (Affine x c) where
  k *^ x = k *< x

instance (Ord x, AbelianAdditive c) => AbelianAdditive (Affine x c)
instance (Ord x, Group c) => Group (Affine x c) where
  negate = fmap negate
instance (Ord x, Additive c) => Additive (Affine x c) where
  (Affine c1 xs1) + (Affine c2 xs2) = Affine (c1 + c2) (xs1 + xs2)
  zero = Affine zero zero

splitVar :: Ord x => Additive c => x -> Affine x c -> (c, Affine x c)
splitVar x (Affine c0 (LinComb m)) = (M.findWithDefault zero x m, Affine c0 (LinComb (M.delete x m)))

-- | @solve x f@ solves the equation @f == 0@ for x.
-- Let f = k x + e.  If k == 0, return Left e. Otherwise, x and return Right -e/k. (The value of x)
solve :: (Eq scalar, Division scalar, Group scalar, Ord x)
      => x -> Affine x scalar -> Either (Affine x scalar) (Affine x scalar)
solve x f = if k == zero then Left e else Right (recip k *^ negate e) 
  where (k,e) = splitVar x f

eval :: forall x c v. (Additive x, Scalable x x) => (c -> x) -> (v -> x) -> Affine v c -> x
eval fc fv (Affine c p) = fc c + LC.eval fc fv p

constant :: Additive c => Ord x => c -> Affine x c
constant c = Affine c zero

subst :: (Ord x, Additive c, Multiplicative c) => (v -> Affine x c) -> Affine v c -> Affine x c
subst f (Affine c p) = constant c + LC.eval id f p 
