{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
module Algebra.Category where

import qualified Prelude
import Data.Kind (Constraint, Type)

-- | A class for categories. Instances should satisfy the laws
--
-- @
-- f '.' 'id'  =  f  -- (right identity)
-- 'id' '.' f  =  f  -- (left identity)
-- f '.' (g '.' h)  =  (f '.' g) '.' h  -- (associativity)
-- @
class Category (cat :: k -> k -> Type) where
  type Con (a :: k) :: Constraint
  type Con a = ()
  (.) :: (Con a, Con b, Con c) => b `cat` c -> a `cat` b -> a `cat` c
  id :: Con a => a `cat` a

instance Category (->) where
  (.) = (Prelude..)
  id = Prelude.id

infixr 9 .
