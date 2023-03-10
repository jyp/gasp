{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
module Algebra.Morphism.MacLaurin (var, ML (..), deriv, integral) where

import Prelude (Int, String, Eq(..), Ord(..),Show(..), Functor(..), (.), Float, Maybe(..),error,otherwise)
import Data.List (intercalate, zipWith,length,take,replicate)
import Data.Monoid
import Algebra.Linear
import Algebra.Classes
import Data.Map (Map)
import qualified Data.Map as M
import Control.Applicative

import Algebra.Morphism.PowerSeries (PS(..))


fromPS' :: Ring a => a -> a -> [a] -> [a]
fromPS' _ _ [] = []
fromPS' n p (f:fs) = f*p : fromPS' (n+1) (p*n) fs

fromPS :: Ring a => PS a -> ML a
fromPS = ML . fromPS' 1 1 . unPS

toPS' :: Field a => a -> a -> [a] -> [a]
toPS' _ _ [] = []
toPS' n p (f:fs) = f/p : toPS' (n+1) (p*n) fs

toPS :: Field a => ML a -> PS a
toPS = PS . toPS' 1 1 . unML

-- >>> fromPS (PS [0,1]^+5)
-- <interactive>:3484:2-21: warning: [-Wtype-defaults]
--     • Defaulting the following constraints to type ‘integer-gmp-1.0.3.0:GHC.Integer.Type.Integer’
--         (Show a0)
--           arising from a use of ‘System.IO.print’ at <interactive>:3484:2-21
--         (Ring a0) arising from a use of ‘it’ at <interactive>:3484:2-21
--         (GHC.Num.Num a0)
--           arising from a use of ‘it’ at <interactive>:3484:2-21
--     • In a stmt of an interactive GHCi command: System.IO.print it
-- [0, 0, 0, 0, 0, 120]

-- | where an empty power series is the series 0, 0, ...
newtype ML a = ML {unML :: [a]}
  deriving (Functor)

instance (Show a) => Show (ML a) where
  show = showML 20 show

showML :: Int -> (t -> String) -> ML t -> String
showML n sho (ML as0)  = "[" <> intercalate ", " (sho <$> as) <> (if length as == n then "..." else "") <> "]"
  where as = take n as0

-- | Head and tail of power series
uncons :: Additive a => ML a -> (a, ML a)
uncons (ML (a:as)) = (a, ML as)
uncons (ML _) = (zero, ML [])

cons :: a -> ML a -> ML a
cons a (ML as) = ML (a:as)

pattern Nil :: forall a. ML a
pattern Nil = ML []

pattern (:.) :: forall a. Additive a => a -> ML a -> ML a
pattern (:.) f fs <- (uncons -> (f, fs)) -- destruction
  where (:.) f fs = cons f fs            -- construction

infixr 5 :.

var :: Ring a => ML a
var = ML [0,1]

instance Additive a => Additive  (ML a) where
  zero = Nil
  Nil + gs = gs
  fs + Nil = fs
  (f :. fs) + (g :. gs) = (f + g) :. (fs + gs)
instance AbelianAdditive a => AbelianAdditive  (ML a) where
instance Group a => Group (ML a) where
  negate = fmap negate

instance Field a => Multiplicative (ML a) where
  one = one :. Nil
  p * q = fromPS (toPS p * toPS q)
  
instance Field a => Module (ML a) (ML a) where
  (*^) = (*)
instance Field a => Ring (ML a) where
  fromInteger n = ML [fromInteger n]


instance (Eq a, Field a) => Division (ML a) where
  Nil / gs = Nil
  (f :. fs) / (g :. gs)
    | g == 0, f == 0 = fs / gs -- if g == 0 then division can only succeed if f == 0
    | g == 0 = error "(/): division by 0"
    | otherwise = let q = f / g in q :. ((fs - q *< gs) / (g :. gs))

instance (Eq a, Field a) => Field (ML a) where
  fromRational r = ML [fromRational r]


deriv :: (Ring t) => ML t -> ML t
deriv (ML []) = zero
deriv (ML (_ : fs)) = ML fs

integral :: (Field t) => ML t -> ML t
integral (ML fs) = ML (0 : fs)

expx :: Field a => ML a
expx = 1 + integral expx

-- >>> expx
-- [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0...]

sinx, cosx :: Field a => ML a
sinx = integral cosx
cosx = 1 - integral sinx

-- >>> sinx + cosx
-- <interactive>:3598:2-12: warning: [-Wtype-defaults]
--     • Defaulting the following constraints to type ‘ghc-prim-0.6.1:GHC.Types.Double’
--         (Show a0)
--           arising from a use of ‘System.IO.print’ at <interactive>:3598:2-12
--         (Field a0) arising from a use of ‘it’ at <interactive>:3598:2-12
--     • In a stmt of an interactive GHCi command: System.IO.print it
-- [1.0, 1.0, -1.0, -1.0, 1.0, 1.0, -1.0, -1.0, 1.0, 1.0, -1.0, -1.0, 1.0, 1.0, -1.0, -1.0, 1.0, 1.0, -1.0, -1.0...]

sqrt :: (Eq a, Field a) => ML a -> ML a
sqrt (0 :. 0 :. fs) = 0 :. sqrt fs
sqrt (1 :. fs) = let qs = 1 + integral ((deriv (1 :. fs)) / (2 *< qs)) in qs
sqrt _ = error "sqrt': first terms wrong"


-- | Composition
compose :: (Eq a, Field a) => ML a -> ML a -> ML a
compose (f :. fs) (g :. gs)
  | g == 0    = f :. (gs * (compose fs (g :. gs)))
  | otherwise = error "compose: first term not 0"

gaussian :: ML Float
gaussian = expx `compose` (- var ^+ 2) 

-- >>> gaussian
-- [1.0, -0.0, -2.0, 0.0, 12.0, -0.0, -120.0, 0.0, 1680.0, -0.0, -30240.0, 0.0, 665280.06, -0.0, -1.7297282e7, 0.0, 5.1891846e8, -0.0, -1.7643227e10, 0.0...]



-- >>> one/(one+var)
-- [1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0...]
