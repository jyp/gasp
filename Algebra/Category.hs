{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
module Algebra.Category where

import qualified Prelude
import Data.Kind (Constraint, Type)

class Category (cat :: k -> k -> Type) where
  type Con (a :: k) :: Constraint
  type Con a = ()
  (.) :: (Con a, Con b, Con c) => b `cat` c -> a `cat` b -> a `cat` c
  id :: Con a => a `cat` a

instance Category (->) where
  (.) = (Prelude..)
  id = Prelude.id

