{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algebra.Morphism.LinComb where

import Prelude (Int, Eq(..), Ord(..),Show(..), Functor(..), fromIntegral, all,id,not,(.),(||),snd,Foldable)
import Data.List (intercalate,and,filter)
import Algebra.Classes
import qualified Data.Map as M
import Data.Function (on)
import Data.Monoid
import Control.Applicative
import Data.Traversable

-- | Normalised linear combinations as maps from variables to
-- coefficients (zero coefficient never present in the map)
newtype LinComb x c = LinComb {fromLinComb :: M.Map x c}
  deriving (Functor,AbelianAdditive,Group,Eq,Ord,Show,Traversable,Foldable)

eval :: forall d x c v. Scalable d x => Additive x => (c -> d) -> (v -> x) -> LinComb v c -> x
eval fc fv p = sum [ fc c *^ fv v | (v, c) <- toList p ]

normalise :: DecidableZero c => LinComb x c -> LinComb x c
normalise (LinComb x) = LinComb (M.filter (not . isZero) x)

instance (Additive c,DecidableZero c,Ord e) => Additive (LinComb e c) where
  zero = LinComb zero
  LinComb x + LinComb y = normalise (LinComb (x+y))

-- Alternative instances for non-normalised version:
-- instance (Eq e, Eq c, Additive c) => Eq (LinComb e c) where
--    (==) = (==) `on` toList

-- instance (Ord e, Ord c, Additive c) => Ord (LinComb e c) where
--    compare = compare `on` toList

toList :: LinComb k a -> [(k, a)]
toList = {- filter ((/= zero) . snd)  no need to filter zeros because normalised -} M.assocs . fromLinComb 

var :: Multiplicative c => x -> LinComb x c
var x = LinComb (M.singleton x one)

-- | Convert from list without testing coefficients
unsafeFromList :: Ord v => [(v,c)] -> LinComb v c
unsafeFromList = LinComb . M.fromList

fromList :: DecidableZero c => Additive c => Ord v => [(v,c)] -> LinComb v c
fromList = normalise . LinComb . M.fromListWith (+)

instance (Eq c, DecidableZero c, Ord e) => DecidableZero (LinComb e c) where
  isZero (LinComb p) = all isZero (M.elems p) 

-- instance (Show c, Show e, Eq c, Multiplicative c) => Show (LinComb e c) where
--   show (LinComb xs) = intercalate "+" ([(if coef /= one then show coef else mempty) <> show m  | (m,coef) <- M.toList xs])

-- | Substitution by evaluation
subst :: DecidableZero c => Additive c => Scalable c c => Ord v => (x -> LinComb v c) -> LinComb x c -> LinComb v c
subst f = eval id f

-- | transform variables. coefficients are not touched
mapVars :: Ord x => (t -> x) -> LinComb t c -> LinComb x c
mapVars f (LinComb m) = unsafeFromList [(f x, e) | (x,e) <- M.assocs m]

-- | Multiplies elements, assuming multiplication is monotonous.
mulVarsMonotonic :: Multiplicative x => x -> LinComb x c -> LinComb x c
mulVarsMonotonic x (LinComb m) = LinComb (M.mapKeysMonotonic (x *) m) 

-- | transform variables with effect. coefficients are not touched
traverseVars :: Applicative f => Ord x => (v -> f x) -> LinComb v c -> f (LinComb x c)
traverseVars f e = unsafeFromList <$> traverse (\(x,c) -> (,c) <$> f x) (toList e)

-- | transform variables and coefficients with effect.
bitraverse :: Applicative f => Ord x => (v -> f x) -> (c -> f d) -> LinComb v c -> f (LinComb x d)
bitraverse f g e = unsafeFromList <$> traverse (\(x,c) -> (,) <$> f x <*> g c) (toList e)
