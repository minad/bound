{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
-- 'Scope' provides a single traditional de Bruijn level
-- and is often used inside of the definition of binders.
--
----------------------------------------------------------------------------
module Bound.Scope.Simple
  (Scope(..)
  -- * Abstraction
  , abstract, abstract1
  -- * Instantiation
  , instantiate, instantiate1
  -- * Alternative names for 'unscope'/'Scope'
  , fromScope
  , toScope
  -- * Bound variable manipulation
  , splat
  , bindings
  , mapBound
  , mapScope
  , foldMapBound
  , foldMapScope
  , traverseBound_
  , traverseScope_
  , traverseBound
  , traverseScope
  , hoistScope
  , bitraverseScope
  , bitransverseScope
  , transverseScope
  , instantiateVars
  ) where

import Bound.Class
import Bound.Var
import Control.DeepSeq (NFData)
import Control.Monad (ap)
import Control.Monad.Trans.Class
import Data.Bifoldable
import Data.Bifunctor
import Data.Binary (Binary)
import Data.Bitraversable
import Data.Foldable
import Data.Functor.Classes
import Data.Hashable
import Data.Hashable.Lifted
import GHC.Generics

-------------------------------------------------------------------------------
-- Scopes
-------------------------------------------------------------------------------

-- | @'Scope' b f a@ is an @f@ expression with bound variables in @b@,
-- and free variables in @a@
--
-- This implements traditional de Bruijn indices, while 'Bound.Scope'
-- implements generalized de Bruijn indices.
--
-- These traditional indices can be used to test the performance gain
-- of generalized indices.
--
-- While this type 'Scope' is identical to 'Control.Monad.Trans.EitherT'
-- this module focuses on a drop-in replacement for 'Bound.Scope'.
--
-- Another use case is for syntaxes not stable under substitution,
-- therefore with only a 'Functor' instance and no 'Monad' instance.
newtype Scope b f a = Scope { unscope :: f (Var b a) }
  deriving (Generic, Generic1, Functor, Foldable, Traversable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Monad f => Applicative (Scope b f) where
  pure a = Scope (pure (F a))
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

-- | The monad permits substitution on free variables, while preserving
-- bound variables
instance Monad f => Monad (Scope b f) where
  Scope e >>= f = Scope $ e >>= \v -> case v of
    B b -> pure (B b)
    F a -> unscope (f a)
  {-# INLINE (>>=) #-}

instance MonadTrans (Scope b) where
  lift ma = Scope (fmap F ma)
  {-# INLINE lift #-}

instance (Eq b, Eq1 f) => Eq1 (Scope b f)  where
  liftEq f m n = liftEq (liftEq f) (unscope m) (unscope n)

instance (Ord b, Ord1 f) => Ord1 (Scope b f) where
  liftCompare f m n = liftCompare (liftCompare f) (unscope m) (unscope n)

instance (Show b, Show1 f) => Show1 (Scope b f) where
  liftShowsPrec f g d m = showParen (d > 10) $
    showString "Scope " . liftShowsPrec (liftShowsPrec f g) (liftShowList f g) 11 (unscope m)

instance (Read b, Read1 f) => Read1 (Scope b f) where
  liftReadsPrec f g d = readParen (d > 10) $ \r -> do
    ("Scope", r') <- lex r
    (s, r'') <- liftReadsPrec (liftReadsPrec f g) (liftReadList f g) 11 r'
    pure (Scope s, r'')

instance (Eq b, Eq1 f, Eq a) => Eq (Scope b f a) where
  (==) = eq1

instance (Ord b, Ord1 f, Ord a) => Ord (Scope b f a) where
  compare = compare1

instance (Show b, Show1 f, Show a) => Show (Scope b f a) where
  showsPrec = showsPrec1

instance (Read b, Read1 f, Read a) => Read (Scope b f a) where
  readsPrec = readsPrec1

instance Bound (Scope b) where
  Scope m >>>= f = Scope $ m >>= \v -> case v of
    B b -> pure (B b)
    F a -> fmap F (f a)
  {-# INLINE (>>>=) #-}

instance (Hashable b, Hashable1 f) => Hashable1 (Scope b f) where
  liftHashWithSalt h n m = liftHashWithSalt (liftHashWithSalt h) n (unscope m)
  {-# INLINE liftHashWithSalt #-}

instance (Hashable b, Hashable1 f, Hashable a) => Hashable (Scope b f a) where
  hashWithSalt n m = hashWithSalt1 n (unscope m)
  {-# INLINE hashWithSalt #-}

-------------------------------------------------------------------------------
-- Abstraction
-------------------------------------------------------------------------------

-- | Capture some free variables in an expression to yield
-- a 'Scope' with bound variables in @b@
--
-- >>> :m + Data.List
-- >>> abstract (`elemIndex` "bar") "barry"
-- Scope [B 0,B 1,B 2,B 2,F 'y']
abstract :: Functor f => (a -> Maybe b) -> f a -> Scope b f a
abstract f e = Scope (fmap k e) where
  k y = case f y of
    Just z  -> B z
    Nothing -> F y
{-# INLINE abstract #-}

-- | Abstract over a single variable
--
-- >>> abstract1 'x' "xyz"
-- Scope [B (),F 'y',F 'z']
abstract1 :: (Functor f, Eq a) => a -> f a -> Scope () f a
abstract1 a = abstract (\b -> if a == b then Just () else Nothing)
{-# INLINE abstract1 #-}

-------------------------------------------------------------------------------
-- Instantiation
-------------------------------------------------------------------------------

-- | Enter a scope, instantiating all bound variables
--
-- >>> :m + Data.List
-- >>> instantiate (\x -> [toEnum (97 + x)]) $ abstract (`elemIndex` "bar") "barry"
-- "abccy"
instantiate :: Monad f => (b -> f a) -> Scope b f a -> f a
instantiate k e = unscope e >>= \v -> case v of
  B b -> k b
  F a -> pure a
{-# INLINE instantiate #-}

-- | Enter a 'Scope' that binds one variable, instantiating it
--
-- >>> instantiate1 "x" $ Scope [B (),F 'y',F 'z']
-- "xyz"
instantiate1 :: Monad f => f a -> Scope n f a -> f a
instantiate1 e = instantiate (const e)
{-# INLINE instantiate1 #-}

hoistScope :: (f (Var b a) -> g (Var b a)) -> Scope b f a -> Scope b g a
hoistScope f = Scope . f . unscope
{-# INLINE hoistScope #-}

-------------------------------------------------------------------------------
-- Compatibility with Bound.Scope
-------------------------------------------------------------------------------

-- | @'fromScope'@ is just another name for 'unscope' and is exported
-- to mimick 'Bound.Scope.fromScope'.
-- In particular no 'Monad' constraint is required.
fromScope :: Scope b f a -> f (Var b a)
fromScope = unscope
{-# INLINE fromScope #-}

-- | @'toScope'@ is just another name for 'Scope' and is exported
-- to mimick 'Bound.Scope.toScope'.
-- In particular no 'Monad' constraint is required.
toScope :: f (Var b a) -> Scope b f a
toScope = Scope
{-# INLINE toScope #-}

-------------------------------------------------------------------------------
-- Exotic Traversals of Bound Variables (not exported by default)
-------------------------------------------------------------------------------

-- | Perform substitution on both bound and free variables in a 'Scope'.
splat :: Monad f => (a -> f c) -> (b -> f c) -> Scope b f a -> f c
splat f unbind s = unscope s >>= \v -> case v of
  B b -> unbind b
  F a -> f a
{-# INLINE splat #-}

-- | Return a list of occurences of the variables bound by this 'Scope'.
bindings :: Foldable f => Scope b f a -> [b]
bindings (Scope s) = foldr f [] s where
  f (B v) vs = v : vs
  f _ vs     = vs
{-# INLINE bindings #-}

-- | Perform a change of variables on bound variables.
mapBound :: Functor f => (b -> b') -> Scope b f a -> Scope b' f a
mapBound f (Scope s) = Scope (fmap f' s) where
  f' (B b) = B (f b)
  f' (F a) = F a
{-# INLINE mapBound #-}

-- | Perform a change of variables, reassigning both bound and free variables.
mapScope :: Functor f => (b -> d) -> (a -> c) -> Scope b f a -> Scope d f c
mapScope f g (Scope s) = Scope $ fmap (bimap f g) s
{-# INLINE mapScope #-}

-- | Obtain a result by collecting information from both bound and free
-- variables
foldMapBound :: (Foldable f, Monoid r) => (b -> r) -> Scope b f a -> r
foldMapBound f (Scope s) = foldMap f' s where
  f' (B a) = f a
  f' _     = mempty
{-# INLINE foldMapBound #-}

-- | Obtain a result by collecting information from both bound and free
-- variables
foldMapScope :: (Foldable f, Monoid r) =>
                (b -> r) -> (a -> r) -> Scope b f a -> r
foldMapScope f g (Scope s) = foldMap (bifoldMap f g) s
{-# INLINE foldMapScope #-}

-- | 'traverse_' the bound variables in a 'Scope'.
traverseBound_ :: (Applicative g, Foldable f) =>
                  (b -> g d) -> Scope b f a -> g ()
traverseBound_ f (Scope s) = traverse_ f' s
  where f' (B a) = () <$ f a
        f' _     = pure ()
{-# INLINE traverseBound_ #-}

-- | 'traverse' both the variables bound by this scope and any free variables.
traverseScope_ :: (Applicative g, Foldable f) =>
                  (b -> g d) -> (a -> g c) -> Scope b f a -> g ()
traverseScope_ f g (Scope s) = traverse_ (bitraverse_ f g) s
{-# INLINE traverseScope_ #-}

-- | Traverse both bound and free variables
traverseBound :: (Applicative g, Traversable f) =>
                 (b -> g c) -> Scope b f a -> g (Scope c f a)
traverseBound f (Scope s) = Scope <$> traverse f' s where
  f' (B b) = B <$> f b
  f' (F a) = pure (F a)
{-# INLINE traverseBound #-}

-- | Traverse both bound and free variables
traverseScope :: (Applicative g, Traversable f) =>
                 (b -> g d) -> (a -> g c) -> Scope b f a -> g (Scope d f c)
traverseScope f g (Scope s) = Scope <$> traverse (bitraverse f g) s
{-# INLINE traverseScope #-}

-- | This allows you to 'bitraverse' a 'Scope'.
bitraverseScope :: (Bitraversable t, Applicative f) => (k -> f k') -> (a -> f a') -> Scope b (t k) a -> f (Scope b (t k') a')
bitraverseScope f = bitransverseScope (bitraverse f)
{-# INLINE bitraverseScope #-}

-- | This is a higher-order analogue of 'traverse'.
transverseScope :: (Functor f)
                => (forall r. g r -> f (h r))
                -> Scope b g a -> f (Scope b h a)
transverseScope tau (Scope s) = Scope <$> tau s

-- | instantiate bound variables using a list of new variables
instantiateVars :: Monad t => [a] -> Scope Int t a -> t a
instantiateVars as = instantiate (vs !!) where
  vs = map pure as
{-# INLINE instantiateVars #-}

bitransverseScope :: Applicative f => (forall a a'. (a -> f a') ->         t a -> f         (u a'))
                                   ->  forall a a'. (a -> f a') -> Scope b t a -> f (Scope b u a')
bitransverseScope tau f (Scope s) = Scope <$> tau (traverse f) s
{-# INLINE bitransverseScope #-}

instance (Binary b, Binary a, Binary (f (Var b a))) => Binary (Scope b f a)
instance (NFData b, NFData a, NFData (f (Var b a))) => NFData (Scope b f a)
