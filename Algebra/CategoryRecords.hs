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

module Algebra.CategoryRecords where


data CategoryRec con cat = CategoryRec{
  (∘)      :: forall a b c. (con a, con b, con c) => b `cat` c -> a `cat` b -> a `cat` c
  ,id :: forall a. con a => a `cat` a
  }
   
data MonoidalRec x i con cat = MonoidalRec
  {(⊗) :: forall a b c d. (con a, con b, con c, con d) => (a `cat` b) -> (c `cat` d) -> (a `x` c) `cat` (b `x` d)
  ,assoc     :: forall a b c. (con a, con b, con c) => ((a `x` b) `x` c) `cat` (a `x` (b `x` c))
  ,assoc_    :: forall a b c. (con a, con b, con c) => (a `x` (b `x` c)) `cat` ((a `x` b) `x` c)
  ,unitorR   :: forall a. (con a,con i) => a `cat` (a `x` i)
  ,unitorR_  :: forall a. (con a,con i) => (a `x` i) `cat` a
  ,unitorL   :: forall a. (con a, con i) => a `cat` (i `x` a)
  ,unitorL_  :: forall a. (con a, con i) => (i `x` a) `cat` a
  }

data BraidedRec x i con cat = BraidedRec
  {swap, swap_ :: forall a b. (con a, con b) => (a `x` b) `cat` (b `x` a)
  }

data CartesianRec x i con cat = CartesianRec
  {exl   ::   forall a b. (con a, con b)                     =>    (a `x` b) `cat` a
  ,exr   ::   forall a b. (con a, con b)                     =>    (a `x` b) `cat` b
  ,dis   ::   forall a.  con a                       =>    a `cat` i
  ,dup   ::   forall a. con a                        =>    a `cat` (a `x` a)
  ,(▵)   ::   forall a b c. (con a,con b, con c) =>    (a `cat` b) -> (a `cat` c) -> a `cat` (b `x` c)
  
  }

