{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
module Algebra.Morphism.PowerSeries (var, PS(PS), unPS, deriv, integral) where

import Prelude (Int, String, Eq(..), Ord(..),Show(..), Functor(..), (.), Float, Maybe(..),error,otherwise)
import Data.List (intercalate, zipWith,length,take)
import Data.Monoid
import Algebra.Linear
import Algebra.Classes
import Control.Applicative

-- | where an empty power series is the series 0, 0, ...
newtype PS a = PS {unPS :: [a]}
  deriving (Functor)

instance (Show a) => Show (PS a) where
  show = showPS 20 show

showPS :: Int -> (t -> String) -> PS t -> String
showPS n sho (PS as0)  = "[" <> intercalate ", " (sho <$> as) <> (if length as == n then "..." else "") <> "]"
  where as = take n as0

-- | Head and tail of power series
uncons :: Additive a => PS a -> (a, PS a)
uncons (PS (a:as)) = (a, PS as)
uncons (PS _) = (zero, PS [])

cons :: a -> PS a -> PS a
cons a (PS as) = PS (a:as)

pattern Nil :: forall a. PS a
pattern Nil = PS []

pattern (:.) :: forall a. Additive a => a -> PS a -> PS a
pattern (:.) f fs <- (uncons -> (f, fs)) -- destruction
  where (:.) f fs = cons f fs            -- construction

infixr 5 :.

var :: Ring a => PS a
var = PS [0,1]


-- -- | A "zippy" applicative
-- instance Applicative PS where
--   pure a = PS (repeat a)
--   fs <*> as = PS (zipWith ($) (unPS fs) (unPS as))  -- be careful with finite lists and zip!

instance Additive a => Additive  (PS a) where
  zero = Nil
  Nil + gs = gs
  fs + Nil = fs
  (f :. fs) + (g :. gs) = (f + g) :. (fs + gs)
instance AbelianAdditive a => AbelianAdditive  (PS a) where
instance Group a => Group (PS a) where
  negate = fmap negate

instance Ring a => Multiplicative (PS a) where
  one = one :. Nil
  Nil * _ = Nil
  _ * Nil = Nil
  (f :. fs) * ggs@(g :. gs) = (f * g) :. (f *< gs + fs * ggs)
  
instance Ring a => Module (PS a) (PS a) where
  (*^) = (*)
instance Ring a => Ring (PS a) where
  fromInteger n = PS [fromInteger n]


instance (Eq a, Field a) => Division (PS a) where
  Nil / gs = Nil
  (f :. fs) / (g :. gs)
    | g == 0, f == 0 = fs / gs -- if g == 0 then division can only succeed if f == 0
    | g == 0 = error "powerseries:  division by 0"
    | otherwise = let q = f / g in q :. ((fs - q *< gs) / (g :. gs))

instance (Eq a, Field a) => Field (PS a) where
  fromRational r = PS [fromRational r]

-- | Composition
compose :: (Eq a, Ring a) => PS a -> PS a -> PS a
compose (f :. fs) (g :. gs)
  | g == 0    = f :. (gs * (compose fs (g :. gs)))
  | otherwise = error "powerseries: compose: first term not 0"

-- | Reversion,
-- Given F find R such that F(R(x)) = x
revert :: (Eq a, Field a) => PS a -> PS a
revert (f :. fs)
  | f == 0    = let rs = 0 :. (1 / (compose fs rs)) in rs
  | otherwise = error "powerseries: revert: first term not 0"


deriv :: (Ring t) => PS t -> PS t
deriv (PS []) = zero
deriv (PS (_ : fs)) = PS (zipWith (*) (fromInteger <$> [1..]) fs)

integral :: (Field t) => PS t -> PS t
integral (PS fs) = PS (0 : zipWith (/) fs (fromInteger <$> [1..]))

expx :: Field a => PS a
expx = 1 + integral expx

sinx, cosx :: Field a => PS a
sinx = integral cosx
cosx = 1 - integral sinx

sqrt :: (Eq a, Field a) => PS a -> PS a
sqrt (0 :. 0 :. fs) = 0 :. sqrt fs
sqrt (1 :. fs) = let qs = 1 + integral ((deriv (1 :. fs)) / (2 *< qs)) in qs
sqrt _ = error "sqrt': first terms wrong"



gaussian :: Field a => Eq a => PS a
gaussian = expx `compose` (- var ^+ 2) 

-- >>> integral gaussian
-- <interactive>:3706:2-18: warning: [-Wtype-defaults]
--     • Defaulting the following constraints to type ‘ghc-prim-0.6.1:GHC.Types.Double’
--         (Show t0)
--           arising from a use of ‘System.IO.print’ at <interactive>:3706:2-18
--         (Field t0) arising from a use of ‘it’ at <interactive>:3706:2-18
--         (Eq t0) arising from a use of ‘it’ at <interactive>:3706:2-18
--     • In a stmt of an interactive GHCi command: System.IO.print it
-- [0.0, 1.0, -0.0, -0.3333333333333333, 0.0, 0.1, -0.0, -2.3809523809523808e-2, 0.0, 4.629629629629629e-3, -0.0, -7.575757575757576e-4, 0.0, 1.0683760683760684e-4, -0.0, -1.3227513227513228e-5, 0.0, 1.4589169000933706e-6, -0.0, -1.4503852223150468e-7...]

-- >>> one/(one+var)
-- [1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0...]
