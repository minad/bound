{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
-- The problem with locally nameless approaches is that original names are
-- often useful for error reporting, or to allow for the user in an interactive
-- theorem prover to convey some hint about the domain. A @'Name' n b@ is a value
-- @b@ supplemented with a (discardable) name that may be useful for error
-- reporting purposes. In particular, this name does not participate in
-- comparisons for equality.
--
-- This module is /not/ exported from "Bound" by default. You need to explicitly
-- import it, due to the fact that 'Name' is a pretty common term in other
-- people's code.
----------------------------------------------------------------------------
module Bound.Name
  ( Name(..)
  , _Name
  , name
  , abstractName
  , abstract1Name
  , instantiateName
  , instantiate1Name
  ) where

import Bound.Scope
import Bound.Var
import Control.Comonad
import Control.DeepSeq (NFData)
import Data.Bifunctor.TH
import Data.Binary (Binary)
import Data.Deriving
import Data.Functor.Classes
import Data.Hashable
import Data.Hashable.Lifted
import Data.Profunctor
import GHC.Generics

-------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------

-- |
-- We track the choice of 'Name' @n@ as a forgettable property that does /not/ affect
-- the result of ('==') or 'compare'.
--
-- To compare names rather than values, use @('Data.Function.on' 'compare' 'name')@ instead.
data Name n b = Name n b
  deriving (Show, Read, Generic, Generic1, Functor, Foldable, Traversable)

-- | Extract the 'name'.
name :: Name n b -> n
name (Name n _) = n
{-# INLINE name #-}

-- |
--
-- This provides an 'Iso' that can be used to access the parts of a 'Name'.
--
-- @
-- '_Name' :: Iso ('Name' n a) ('Name' m b) (n, a) (m, b)
-- @
_Name :: (Profunctor p, Functor f) => p (n, a) (f (m,b)) -> p (Name n a) (f (Name m b))
_Name = dimap (\(Name n a) -> (n, a)) (fmap (uncurry Name))
{-# INLINE _Name #-}

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Eq b => Eq (Name n b) where
  Name _ a == Name _ b = a == b
  {-# INLINE (==) #-}

instance Hashable2 Name where
  liftHashWithSalt2 _ h s (Name _ a) = h s a
  {-# INLINE liftHashWithSalt2 #-}

instance Hashable1 (Name n) where
  liftHashWithSalt h s (Name _ a) = h s a
  {-# INLINE liftHashWithSalt #-}

instance Hashable a => Hashable (Name n a) where
  hashWithSalt m (Name _ a) = hashWithSalt m a
  {-# INLINE hashWithSalt #-}

instance Ord b => Ord (Name n b) where
  Name _ a `compare` Name _ b = compare a b
  {-# INLINE compare #-}

instance Comonad (Name n) where
  extract (Name _ b) = b
  {-# INLINE extract #-}
  extend f w@(Name n _) = Name n (f w)
  {-# INLINE extend #-}

instance Eq2 Name where
  liftEq2 _ g (Name _ b) (Name _ d) = g b d

instance Ord2 Name where
  liftCompare2 _ g (Name _ b) (Name _ d) = g b d

instance Eq1 (Name b) where
  liftEq f (Name _ b) (Name _ d) = f b d

instance Ord1 (Name b) where
  liftCompare f (Name _ b) (Name _ d) = f b d

instance (Binary b, Binary a) => Binary (Name b a)
instance (NFData b, NFData a) => NFData (Name b a)

deriveShow2 ''Name
deriveRead2 ''Name
deriveShow1 ''Name
deriveRead1 ''Name
deriveBifunctor ''Name
deriveBifoldable ''Name
deriveBitraversable ''Name

-------------------------------------------------------------------------------
-- Abstraction
-------------------------------------------------------------------------------

-- | Abstraction, capturing named bound variables.
abstractName :: Monad f => (a -> Maybe b) -> f a -> Scope (Name a b) f a
abstractName f t = Scope (fmap k t) where
  k a = case f a of
    Just b  -> B (Name a b)
    Nothing -> F (return a)
{-# INLINE abstractName #-}

-- | Abstract over a single variable
abstract1Name :: (Monad f, Eq a) => a -> f a -> Scope (Name a ()) f a
abstract1Name a = abstractName (\b -> if a == b then Just () else Nothing)
{-# INLINE abstract1Name #-}

-------------------------------------------------------------------------------
-- Instantiation
-------------------------------------------------------------------------------

-- | Enter a scope, instantiating all bound variables, but discarding (comonadic)
-- meta data, like its name
instantiateName :: (Monad f, Comonad n) => (b -> f a) -> Scope (n b) f a -> f a
instantiateName k e = unscope e >>= \v -> case v of
  B b -> k (extract b)
  F a -> a
{-# INLINE instantiateName #-}

-- | Enter a 'Scope' that binds one (named) variable, instantiating it.
--
-- @'instantiate1Name' = 'instantiate1'@
instantiate1Name :: Monad f => f a -> Scope n f a -> f a
instantiate1Name = instantiate1
{-# INLINE instantiate1Name #-}
