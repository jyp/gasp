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

laws_category :: forall f x i. (Category f) => TestableCat x i (Obj f) f -> Property
laws_category tc@TestableCat {..}
  = product [forallMorphism' @f tc (\f -> property (law_id_comp f))
            ,forallMorphism' @f tc (\f -> property (law_comp_id f))
            ,genObj $ \t1 -> genObj $ \t2 -> genObj $ \t3 -> genObj $ \t4 ->
             genMorph t1 t2 $ \ h -> genMorph t2 t3 $ \ g -> genMorph t3 t4 $ \ f ->
             (f . (g . h) =.= (f . g) . h) \\ getTestable t1 t4]


type TT f x y = TestEqual (f x y)
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

testableCat :: forall f x i o obj. GenObj obj o f -> (forall a b. o a -> o b -> (f a b -> Property) -> Property) -> ( forall a b. o a -> o b -> Dict (TT f a b)) -> (forall a b. o a -> o b -> o (x a b)) -> o i -> TestableCat x i obj f
testableCat genObj genMorph getTestable (×) unitObj = TestableCat{..}
  where genMorph' :: forall a b. o a -> o b -> (TT f a b => f a b -> Property) -> Property
        genMorph' a b k = genMorph a b $ \f -> k f \\ getTestable a b
        getTestable' :: forall a. o a -> Dict (TT f a a)
        getTestable' a = getTestable a a


law_parallel_composition :: forall {k} {cat :: k -> k -> Type}
                                     {x :: k -> k -> k} {a :: k} {c :: k} {b1 :: k} {b2 :: k}
                                     {b3 :: k} {d :: k} {i :: k} obj.
                              (obj (x a c), obj (x b1 b2), obj (x b3 d), obj a,
                               obj b1, obj b3, obj c, obj b2, obj d, Category cat, Obj cat ~ obj,
                               TestEqual (cat (x a c) (x b3 d))) =>
                              R.MonoidalRec x i obj cat -> cat b1 b3 -> cat b2 d -> cat a b1 -> cat c b2 -> Property
law_parallel_composition R.MonoidalRec{..} e f g h = nameLaw "cross-comp" ((e ⊗ f) ∘ (g ⊗ h) =.= (e ∘ g) ⊗ (f ∘ h))

law_assoc_inv :: forall {k} (a::k) (b::k) (c::k) x i obj (cat :: k -> k -> Type) o.
  (obj a, obj b, obj c, Con' x obj, TestEqual (cat (x (x a b) c) (x (x a b) c)), Category cat, Obj cat ~ obj)
  => R.MonoidalRec x i obj cat -> o a -> o b -> o c -> Property
law_assoc_inv R.MonoidalRec{..} _ _ _ = nameLaw "assoc-inv" (assoc_ @a @b @c ∘ assoc =.= id)
  

law_unitorR_inv :: forall {k} (cat :: k -> k -> Type) x i {b :: k} {con :: k -> Constraint} {o}.
                     (Monoidal x i cat, Obj cat ~ con, Con' x con, con ~ Obj cat,  con b, con i,
                      TestEqual (cat (x b i) (x b i))) =>
                     o b -> Property
law_unitorR_inv _ = nameLaw "unitor-inv" ((unitorR :: b `cat` (b `x` i)) ∘ unitorR_ =.= id)


law_unitorL_inv :: forall {k} {cat :: k -> k -> Type}
                            {x :: k -> k -> k} {b :: k} {i :: k} {con :: k -> Constraint} {o}.
                     (Category cat, Obj cat ~ con, Con' x con, con ~ Obj cat,  con b, con i,
                      TestEqual (cat (x i b) (x i b))) =>
                     R.MonoidalRec x i con cat -> o b -> Property
law_unitorL_inv  R.MonoidalRec{..} _ = nameLaw "unitor_-inv" (unitorL @b ∘ unitorL_ =.= id)
  
law_monoidal_triangle :: forall {k} (cat :: k -> k -> Type) (x :: k -> k -> k) (i :: k) a c obj o. (obj ~ Obj cat, Monoidal x i cat, obj a, obj c, obj i, Con' x obj, TestEqual (cat (x a c) (x a (x i c))))
  => o a -> o c -> Property
law_monoidal_triangle _ _ = nameLaw "monoidal-triangle"
   ((assoc . (unitorR ⊗ id)) =.=  ((id ⊗ unitorL) :: (cat (x a c) (x a (x i c)))))

law_monoidal_pentagon :: forall {k} (cat :: k -> k -> Type) (x :: k -> k -> k) (i :: k) a b c d obj o.
   (obj ~ Obj cat, Monoidal x i cat, obj a, obj b, obj c, obj d, Con' x obj, (TestEqual (cat (x (x (x a b) c) d) (x a (x b (x c d))))))
  => o a -> o b -> o c -> o d -> Property
law_monoidal_pentagon _ _ _ _ = nameLaw "monoidal-pentagon"
   (assoc . assoc =.=  ((id ⊗ assoc) . assoc . (assoc ⊗ id)
                        :: (cat (x (x (x a b) c) d) (x a (x b (x c d))))))


laws_monoidal :: forall {k} (cat :: k -> k -> Type) x i (obj :: k -> Constraint).
                 (obj ~ Obj cat, Con' x obj, Monoidal x i cat, obj i) 
                 => TestableCat x i obj cat -> Property
laws_monoidal  t@TestableCat{..}   = product
   [ laws_category t
   , genObj $ \t1 -> genObj $ \t2 -> genObj $ \t3 ->
     genObj $ \t4 -> genObj $ \t5 -> genObj $ \t6 ->
     genMorph t1 t2 $ \e -> genMorph t2 t3 $ \f ->
     genMorph t4 t5 $ \g -> genMorph t5 t6 $ \h ->
     law_parallel_composition m f h e g
     \\ getTestable (t1 × t4) (t3 × t6)
   , genObj $ \a -> genObj $ \b -> genObj $ \c -> law_assoc_inv m  a b c
     \\ getTestable' ((a × b) × c)
   , genObj $ \a -> genObj $ \b -> genObj $ \c -> law_assoc_inv mOp a b c
     \\ getTestable' ((a × b) × c)
   , genObj $ \a -> law_unitorR_inv @cat @x a \\ getTestable' (a × unitObj) 
   , genObj $ \a -> law_unitorR_inv @(Op cat) @x a  \\ getTestable' (a × unitObj)
   , genObj $ \a -> law_unitorL_inv m   a  \\ getTestable' (unitObj × a)
   , genObj $ \a -> law_unitorL_inv mOp a  \\ getTestable' (unitObj × a)
   , genObj $ \a -> genObj $ \b -> law_monoidal_triangle @cat @x a b
     \\ getTestable (a × b) (a × (unitObj × b))
   , genObj $ \a -> genObj $ \b -> genObj $ \c -> genObj $ \d ->
       law_monoidal_pentagon @cat @x a b c d
       \\ getTestable (((a × b) × c) × d) (a × (b × (c × d))) 
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

law_braided_hexagon1 :: forall {k} (cat :: k -> k -> Type) x i a b c obj o.
   (obj ~ Obj cat, Braided x i cat, obj a, obj b, obj c, Con' x obj, (TestEqual (cat (x (x a b) c) (x b (x c a)))))
  => o a -> o b -> o c -> Property
law_braided_hexagon1 _ _ _ = nameLaw "braided-hexagon-1"
   (assoc . swap . assoc =.= ((id ⊗ swap) . assoc . (swap ⊗ id)
      :: cat ((a `x` b) `x` c) (b `x` (c `x` a))))

law_braided_hexagon2 :: forall {k} (cat :: k -> k -> Type) x i a b c obj o.
   (obj ~ Obj cat, Braided x i cat, obj a, obj b, obj c, Con' x obj, (TestEqual (cat (x a (x b c)) (x (x c a) b))))
  => o a -> o b -> o c -> Property
law_braided_hexagon2 _ _ _ = nameLaw "braided-hexagon-2"
   (assoc_ . swap . assoc_ =.= ((swap ⊗ id) . assoc_ . (id ⊗ swap) 
      :: cat (a `x` (b `x` c)) ((c `x` a) `x` b)))

law_braided_triangle :: forall {k} (cat :: k -> k -> Type) (x :: k -> k -> k) (i :: k) a obj o. (obj ~ Obj cat, Braided x i cat, obj a, obj i, Con' x obj, TestEqual (cat (x a i) a))
  => o a -> Property
law_braided_triangle _ = nameLaw "monoidal-triangle"
   (unitorL_ . swap =.=  (unitorR_ :: (cat (x a i) a)))


laws_braided :: forall {k} {x :: k -> k -> k}
                          {obj :: k -> Constraint} 
                          {i :: k} 
                          (cat :: k -> k -> Type).
                 (obj ~ Obj cat, Con' x obj, Braided x i cat, obj i) 
                 => TestableCat x i obj cat -> Property
laws_braided  t@TestableCat{..}   = product
   [ laws_monoidal t
   , genObj $ \a -> genObj $ \b -> law_swap_inv m   a b  \\ getTestable' (b × a)
   , genObj $ \a -> genObj $ \b -> law_swap_inv mOp a b  \\ getTestable' (b × a)
   , genObj $ \a -> law_braided_triangle @cat @x a \\ getTestable (a × unitObj) a
   , genObj $ \a -> genObj $ \b -> genObj $ \c ->
       law_braided_hexagon1 @cat @x a b c \\ getTestable ((a × b) × c) (b × (c × a))
   , genObj $ \a -> genObj $ \b -> genObj $ \c ->
       law_braided_hexagon2 @cat @x a b c \\ getTestable (a × (b × c)) ((c × a) × b)
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


laws_symmetric :: forall {k} {x :: k -> k -> k}
                          {obj :: k -> Constraint} 
                          {i :: k} 
                          (cat :: k -> k -> Type).
                 (obj ~ Obj cat, Con' x obj, Braided x i cat, obj i) 
                 => TestableCat x i obj cat -> Property
laws_symmetric  t@TestableCat{..}   = product
   [ laws_braided t
   , genObj $ \a -> genObj $ \b -> law_swap_invol m a b
      \\ getTestable' (b × a) 
   ]
   where m :: R.BraidedRec x i obj cat 
         m@R.BraidedRec{} = braidedRec @x


law_dup_commut :: forall {k} {cat :: k -> k -> Type}
                                     {x :: k -> k -> k}  {a :: k}
                                     {b :: k} {i :: k} obj.
                              (obj a, obj b, Category cat, Obj cat ~ obj,
                               TestEqual (cat a (x b b)), Cartesian x i cat, Con' x obj) =>
                              R.CartesianRec x i obj cat -> cat a b -> Property
law_dup_commut R.CartesianRec{..} f = nameLaw "dup/cross" ((f ⊗ f) . dup =.= dup . f)

law_projections :: forall {k} {con :: k -> Constraint} {x :: k -> k -> k}
                      {b :: k} {c :: k} {cat :: k -> k -> Type} {i :: k} {p}.
               (con (x b c), con b, con c, Obj cat (x b c), Con' x con,
                TestEqual (cat (x b c) (x b c)), Category cat) =>
               R.CartesianRec x i con cat -> p b -> p c -> Property
law_projections R.CartesianRec{..} _ _ = nameLaw "projections" (exl ▵ exr  =.= id @k @cat @(b `x` c))



laws_cartesian_extra :: forall {k} (x :: k -> k -> k)
                          {obj :: k -> Constraint} 
                          (i :: k )
                          (cat :: k -> k -> Type).
                 (obj ~ Obj cat, Con' x obj, Cartesian x i cat, obj i) 
                 => TestableCat x i obj cat -> Property
laws_cartesian_extra  t@TestableCat{..}   = product
   [ genObj $ \t1 -> genObj $ \t2 -> genMorph t1 t2 $ \f -> law_dup_commut m f  \\ getTestable t1 (t2 × t2)
   , genObj $ \t1 -> genObj $ \t2 -> law_projections m t1 t2  \\ getTestable' (t1 × t2)
   ]
   where m :: R.CartesianRec x i obj cat 
         m@R.CartesianRec{..} = cartesianRec

laws_cartesian :: forall {k} (x :: k -> k -> k)
                          {obj :: k -> Constraint} 
                          (i :: k )
                          (cat :: k -> k -> Type).
                 (obj ~ Obj cat, Con' x obj, Cartesian x i cat, obj i) 
                 => TestableCat x i obj cat -> Property
laws_cartesian  t@TestableCat{..} = product
   [ laws_symmetric t , laws_cartesian_extra t]

laws_cocartesian :: forall {k} {x :: k -> k -> k}
                          {obj :: k -> Constraint} 
                          {i :: k} 
                          {cat :: k -> k -> Type}.
                 (obj ~ Obj cat, Con' x obj, CoCartesian x i cat, obj i) 
                 => TestableCat x i obj cat -> Property
laws_cocartesian  t = laws_cartesian (opTestable t)


opTestable :: TestableCat x i obj cat -> TestableCat x i obj (Op cat)
opTestable TestableCat{..} = testableCat
                               genObj (\a b k -> genMorph b a $ \f -> k (Op f))
                               (\a b -> Dict \\ getTestable b a)
                               (×) unitObj

laws_bicartesian :: forall {k} {x :: k -> k -> k}
                          {obj :: k -> Constraint} 
                          {i :: k} 
                          (cat :: k -> k -> Type).
                 (obj ~ Obj cat, Con' x obj, BiCartesian x i cat, obj i) 
                 => TestableCat x i obj cat -> Property
laws_bicartesian  t = product [ laws_symmetric t
                              , laws_cartesian_extra t
                              , laws_cartesian_extra (opTestable t)]
