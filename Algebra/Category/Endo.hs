{-# LANGUAGE UndecidableInstances #-}
module Algebra.Category.Endo where

import Prelude (Semigroup(..), Monoid(..))
import Algebra.Category
import Algebra.Classes

newtype Endo cat a = Endo (cat a a)

instance (Category cat, Obj cat a) => Semigroup (Endo cat a) where
  Endo f <> Endo g = Endo (f . g)

instance (Category cat, Obj cat a) => Monoid (Endo cat a) where
  mempty = Endo id


instance (Category cat, Obj cat a) => Multiplicative (Endo cat a) where
  Endo f * Endo g = Endo (f . g)
  one = Endo id


instance (Dagger cat, Obj cat a) => Division (Endo cat a) where
  recip (Endo m) = Endo (dagger m)


