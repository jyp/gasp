{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algebra.Morphism.LinComb where

import Prelude (Int, Eq(..), Ord(..),Show(..), Functor(..), fromIntegral, all,id,not,(.),(||))
import Data.List (intercalate,and)
import Algebra.Classes
import Data.Map (Map)
import qualified Data.Map as M
import Data.Function (on)
import Data.Monoid

newtype LinComb x c = LC {fromLinComb :: M.Map x c}  deriving (Additive,Functor,AbelianAdditive,Group)

deriving instance (Ord x, Scalable c c) => Scalable c (LinComb x c)

eval :: forall d x c v. Scalable d x => Additive x => (c -> d) -> (v -> x) -> LinComb v c -> x
eval fc fv (LC p) = sum [ fc c *^ fv v | (v, c) <- M.assocs p ]

instance (Eq e, Eq c, Additive c) => Eq (LinComb e c) where
   (==) = (==) `on` (M.filter (/= zero) . fromLinComb)

instance (Ord e, Ord c, Additive c) => Ord (LinComb e c) where
   compare = compare `on` (M.filter (/= zero) . fromLinComb)

toList :: LinComb k a -> [(k, a)]
toList = M.assocs . fromLinComb

mapVars :: Ord x => (t -> x) -> LinComb t c -> LinComb x c
mapVars f (LC m) = LC (M.fromList [(f x, e) | (x,e) <- M.assocs m])

var :: Multiplicative c => x -> LinComb x c
var x = LC (M.singleton x one)

fromList :: Additive c => Ord v => [(v,c)] -> LinComb v c
fromList = LC . M.fromListWith (+)

instance (DecidableZero c, Ord e) => DecidableZero (LinComb e c) where
  isZero (LC p) = all isZero (M.elems p) 

instance (Show c, Show e, Eq c, Multiplicative c) => Show (LinComb e c) where
  show (LC xs) = intercalate "+" ([(if coef /= one then show coef else mempty) <> show m  | (m,coef) <- M.toList xs])

-- | Substitution by evaluation
subst :: Additive c => Scalable c c => Ord v => (x -> LinComb v c) -> LinComb x c -> LinComb v c
subst f = eval id f
