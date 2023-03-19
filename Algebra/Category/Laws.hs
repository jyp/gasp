{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Algebra.Category.Laws where

import qualified Algebra.CategoryRecords as R
-- import Algebra.CategoryRecords (MonoidalRec(MonoidalRec))
import Algebra.Category
import Algebra.Category.Op

import Algebra.Classes (nameLaw, TestEqual(..), product)
import Algebra.Category.Objects
import Data.Kind
import Data.Constraint
import Test.QuickCheck
import Prelude (Show(..),($))


law_id_comp :: forall {k} (f :: k -> k -> Type) a b. (Category f, TestEqual (f a b), O2 f a b) => f a b -> Property
law_id_comp n = nameLaw "id/comp" (id . n =.= n)

forallMorphism' :: forall f x i. TestableCat x i (Obj f) f -> (forall a b. (O2 f a b, TT f a b) => f a b -> Property) -> Property
forallMorphism' (TestableCat {..}) p
  = genObj (\t1 -> 
    genObj (\t2 ->
    genMorph' t1 t2 (\f -> p f)))


law_comp_id :: forall {k} (f :: k -> k -> Type) a b. (Category f, TestEqual (f a b), O2 f a b) => f a b -> Property
law_comp_id n = nameLaw "comp/id" (n . id =.= n)

law_comp_assoc :: forall {k} (f :: k -> k -> Type) a b c d. (Category f, TestEqual (f a d), O4 f a b c d) => f c d -> f b c -> f a b -> Property
law_comp_assoc n m o = nameLaw "comp/assoc" (n . (m . o) =.= (n . m) . o)

law_comp_assoc' :: forall {k} (f :: k -> k -> Type) {x} i.
  (-- forall x y. (con x, con y) => TestEqual (f x y),
   -- forall α β. (con α, con β) => Arbitrary (f α β),
   -- forall α β. (con α, con β) => Show (f α β),
   Category f)
  => TestableCat x i (Obj f)  f -> Property
law_comp_assoc' (TestableCat {..})
  = genObj (\t1 ->
    genObj (\t2 ->
    genObj (\t3 ->
    genObj (\t4 ->
    genMorph t1 t2 (\ h ->
    genMorph t2 t3 (\ g ->
    genMorph t3 t4 (\ f ->
    (f . (g . h) =.= (f . g) . h)
    \\ getTestable t1 t4
                   )))))))


laws_category :: forall f x i. (Category f) => TestableCat x i (Obj f) f -> Property
laws_category tc = product [forallMorphism' @f tc (\f -> property (law_id_comp f))
                           ,forallMorphism' @f tc (\f -> property (law_comp_id f))
                           ,law_comp_assoc' tc]


type TT f x y = (Arbitrary (f x y), Show (f x y), TestEqual (f x y))
type GenObj obj o f = ((forall a. obj a => o a -> Property) -> Property)

data TestableCat x i obj f = forall o. TestableCat
  {genObj :: GenObj obj o f
  ,genMorph' :: forall a b. o a -> o b -> (TT f a b => f a b -> Property) -> Property
  ,genMorph :: forall a b. o a -> o b -> (f a b -> Property) -> Property
  ,getTestable :: forall a b. o a -> o b -> Dict (TT f a b)
  ,getTestable' :: forall a. o a -> Dict (TT f a a)
  ,(×) :: forall a b. o a -> o b -> o (a `x` b)
  ,unitObj :: o i
  }


law_parallel_composition :: forall {k} {cat :: k -> k -> Type}
                                     {x :: k -> k -> k} {a :: k} {c :: k} {b1 :: k} {b2 :: k}
                                     {b3 :: k} {d :: k} {i :: k} obj.
                              (obj (x a c), obj (x b1 b2), obj (x b3 d), obj a,
                               obj b1, obj b3, obj c, obj b2, obj d, Category cat, Obj cat ~ obj,
                               TestEqual (cat (x a c) (x b3 d))) =>
                              R.MonoidalRec x i obj cat -> cat b1 b3 -> cat b2 d -> cat a b1 -> cat c b2 -> Property
law_parallel_composition R.MonoidalRec{..} e f g h   = (e ⊗ f) ∘ (g ⊗ h) =.= (e ∘ g) ⊗ (f ∘ h)

law_assoc_inv :: forall {k} (a::k) (b::k) (c::k) x i obj (cat :: k -> k -> Type) o.
  (obj a, obj b, obj c, Con' x obj, TestEqual (cat (x (x a b) c) (x (x a b) c)), Category cat, Obj cat ~ obj)
  => R.MonoidalRec x i obj cat -> o a -> o b -> o c -> Property
law_assoc_inv R.MonoidalRec{..} _ _ _ = nameLaw "assoc-inv" (assoc_ @a @b @c ∘ assoc =.= id)

  
law_unitorR_inv :: forall {k} {cat :: k -> k -> Type}
                            {x :: k -> k -> k} {b :: k} {i :: k} {con :: k -> Constraint} {o}.
                     (Category cat, Obj cat ~ con, Con' x con, con ~ Obj cat,  con b, con i,
                      TestEqual (cat (x b i) (x b i))) =>
                     R.MonoidalRec x i con cat -> o b -> Property
law_unitorR_inv  R.MonoidalRec{..} _ = nameLaw "unitor-inv" (unitorR @b ∘ unitorR_ =.= id)

law_unitorL_inv :: forall {k} {cat :: k -> k -> Type}
                            {x :: k -> k -> k} {b :: k} {i :: k} {con :: k -> Constraint} {o}.
                     (Category cat, Obj cat ~ con, Con' x con, con ~ Obj cat,  con b, con i,
                      TestEqual (cat (x i b) (x i b))) =>
                     R.MonoidalRec x i con cat -> o b -> Property
law_unitorL_inv  R.MonoidalRec{..} _ = nameLaw "unitor_-inv" (unitorL @b ∘ unitorL_ =.= id)


law_monoidal :: forall {k} (cat :: k -> k -> Type) {a :: k} (x :: k -> k -> k) (i :: k) obj o. (obj ~ Obj cat, Monoidal x i cat, TestEqual (a `cat` a), obj a, obj i, Con' x obj )
  => o a -> Property
law_monoidal _ = nameLaw "monoidal" (unitorL_ . (id ⊗ unitorR_) . assoc . (unitorL ⊗ id) . (unitorR :: a `cat` (a `x` i)) =.= id)

laws_monoidal :: forall {k} {x :: k -> k -> k}
                          {obj :: k -> Constraint} 
                          {i :: k} 
                          {cat :: k -> k -> Type}.
                 (obj ~ Obj cat, Con' x obj, Monoidal x i cat, obj i) 
                 => TestableCat x i obj cat -> Property
laws_monoidal  t@TestableCat{..}   = product
   [ laws_category t
   , genObj $ \a -> genObj $ \b -> genObj $ \c -> law_assoc_inv m  a b c \\ getTestable' ((a × b) × c)
   , genObj $ \a -> genObj $ \b -> genObj $ \c -> law_assoc_inv mOp a b c \\ getTestable' ((a × b) × c)
   , genObj $ \a -> law_unitorR_inv m   a \\ getTestable' (a × unitObj)
   , genObj $ \a -> law_unitorR_inv mOp a  \\ getTestable' (a × unitObj)
   , genObj $ \a -> law_unitorL_inv m   a  \\ getTestable' (unitObj × a)
   , genObj $ \a -> law_unitorL_inv mOp a  \\ getTestable' (unitObj × a)
   , genObj $ \a -> law_monoidal @cat @x a \\ getTestable' a
   , genObj $ \a -> law_monoidal @(Op cat) @x a \\ getTestable' a
   ]
   where m :: R.MonoidalRec x i obj cat 
         m@R.MonoidalRec{} = monoidalRec @x
         mOp :: R.MonoidalRec x i obj (Op cat)
         mOp = monoidalRec @x
         -- running the test on the op category mean that we test the reverse compositions.

law_swap_inv :: forall {k} (a::k) (b::k) x i obj (cat :: k -> k -> Type) o.
  (obj ~ Obj cat, Braided x i cat, Con' x obj, obj a, obj b, TestEqual (cat (x b a) (x b a)))
  => R.BraidedRec x i obj cat -> o a -> o b -> Property
law_swap_inv R.BraidedRec{..} _ _ = nameLaw "swap-inv" (swap_ @a @b ∘ swap =.= id)

laws_braided :: forall {k} {x :: k -> k -> k}
                          {obj :: k -> Constraint} 
                          {i :: k} 
                          {cat :: k -> k -> Type}.
                 (obj ~ Obj cat, Con' x obj, Braided x i cat, obj i) 
                 => TestableCat x i obj cat -> Property
laws_braided  t@TestableCat{..}   = product
   [ laws_monoidal t
   , genObj $ \a -> genObj $ \b -> law_swap_inv m   a b  \\ getTestable' (b × a)
   , genObj $ \a -> genObj $ \b -> law_swap_inv mOp a b  \\ getTestable' (b × a)
   ]
   where m :: R.BraidedRec x i obj cat 
         m@R.BraidedRec{} = braidedRec @x
         mOp :: R.BraidedRec x i obj (Op cat)
         mOp = braidedRec @x
         -- running the test on the op category mean that we test the reverse compositions.

law_swap_invol :: forall {k} (a::k) (b::k) x i obj (cat :: k -> k -> Type) o.
  (obj ~ Obj cat, Braided x i cat, Con' x obj, obj a, obj b, TestEqual (cat (x b a) (x b a)))
  => R.BraidedRec x i obj cat -> o a -> o b -> Property
law_swap_invol R.BraidedRec{..} _ _ = nameLaw "swap-invol" (swap @a @b ∘ swap =.= id)


law_dup_commut :: forall {k} {cat :: k -> k -> Type}
                                     {x :: k -> k -> k}  {a :: k}
                                     {b :: k} {i :: k} obj.
                              (obj a, obj b, Category cat, Obj cat ~ obj,
                               TestEqual (cat a (x b b)), Cartesian x i cat, Con' x obj) =>
                              R.CartesianRec x i obj cat -> cat a b -> Property
law_dup_commut R.CartesianRec{..} f = f ▵ f =.= dup . f
