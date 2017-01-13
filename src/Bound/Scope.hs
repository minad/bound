{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2012-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
-- This is the work-horse of the @bound@ library.
--
-- 'Scope' provides a single generalized de Bruijn level
-- and is often used inside of the definition of binders.
----------------------------------------------------------------------------
module Bound.Scope
  ( Scope(..)
  -- * Abstraction
  , abstract, abstract1
  -- * Instantiation
  , instantiate, instantiate1
  -- * Traditional de Bruijn
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
import Control.Monad
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
-- We store bound variables as their generalized de Bruijn
-- representation in that we're allowed to 'lift' (using 'F') an entire
-- tree rather than only succ individual variables, but we're still
-- only allowed to do so once per 'Scope'. Weakening trees permits
-- /O(1)/ weakening and permits more sharing opportunities. Here the
-- deBruijn 0 is represented by the 'B' constructor of 'Var', while the
-- de Bruijn 'succ' (which may be applied to an entire tree!) is handled
-- by 'F'.
--
-- NB: equality and comparison quotient out the distinct 'F' placements
-- allowed by the generalized de Bruijn representation and return the
-- same result as a traditional de Bruijn representation would.
--
-- Logically you can think of this as if the shape were the traditional
-- @f (Var b a)@, but the extra @f a@ inside permits us a cheaper 'lift'.
--
newtype Scope b f a = Scope { unscope :: f (Var b (f a)) }
  deriving (Generic, Generic1, Functor, Foldable, Traversable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Functor f, Monad f) => Applicative (Scope b f) where
  pure a = Scope (pure (F (pure a)))
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

-- | The monad permits substitution on free variables, while preserving
-- bound variables
instance Monad f => Monad (Scope b f) where
  Scope e >>= f = Scope $ e >>= \v -> case v of
    B b -> pure (B b)
    F ea -> ea >>= unscope . f
  {-# INLINE (>>=) #-}

instance MonadTrans (Scope b) where
  lift m = Scope (pure (F m))
  {-# INLINE lift #-}

instance (Monad f, Eq b, Eq1 f, Eq a) => Eq (Scope b f a) where (==) = eq1
instance (Monad f, Ord b, Ord1 f, Ord a) => Ord (Scope b f a) where compare = compare1

--------------------------------------------------------------------------------
-- * transformers 0.5 Data.Functor.Classes
--------------------------------------------------------------------------------

instance (Show b, Show1 f) => Show1 (Scope b f) where
  liftShowsPrec f g d m = showsUnaryWith (liftShowsPrec (liftShowsPrec f' g') (liftShowList f' g')) "Scope" d (unscope m) where
    f' = liftShowsPrec f g
    g' = liftShowList f g

instance (Read b, Read1 f) => Read1 (Scope b f) where
  liftReadsPrec f g = readsData $ readsUnaryWith (liftReadsPrec (liftReadsPrec f' g') (liftReadList f' g')) "Scope" Scope where
    f' = liftReadsPrec f g
    g' = liftReadList f g

instance (Read b, Read1 f, Read a) => Read  (Scope b f a) where readsPrec = readsPrec1
instance (Show b, Show1 f, Show a) => Show (Scope b f a) where showsPrec = showsPrec1

instance (Monad f, Eq b, Eq1 f) => Eq1 (Scope b f) where
  liftEq f m n = liftEq (liftEq f) (fromScope m) (fromScope n)

instance (Monad f, Ord b, Ord1 f) => Ord1 (Scope b f) where
  liftCompare f m n = liftCompare (liftCompare f) (fromScope m) (fromScope n)

instance Bound (Scope b) where
  Scope m >>>= f = Scope (fmap (fmap (>>= f)) m)
  {-# INLINE (>>>=) #-}

instance (Hashable b, Monad f, Hashable1 f) => Hashable1 (Scope b f) where
  liftHashWithSalt h s m = liftHashWithSalt (liftHashWithSalt h) s (fromScope m)
  {-# INLINE liftHashWithSalt #-}

instance (Hashable b, Monad f, Hashable1 f, Hashable a) => Hashable (Scope b f a) where
  hashWithSalt n m = hashWithSalt1 n (fromScope m)
  {-# INLINE hashWithSalt #-}

-------------------------------------------------------------------------------
-- Abstraction
-------------------------------------------------------------------------------

-- | Capture some free variables in an expression to yield
-- a 'Scope' with bound variables in @b@
--
-- >>> :m + Data.List
-- >>> abstract (`elemIndex` "bar") "barry"
-- Scope [B 0,B 1,B 2,B 2,F "y"]
abstract :: Monad f => (a -> Maybe b) -> f a -> Scope b f a
abstract f e = Scope (fmap k e) where
  k y = case f y of
    Just z  -> B z
    Nothing -> F (pure y)
{-# INLINE abstract #-}

-- | Abstract over a single variable
--
-- >>> abstract1 'x' "xyz"
-- Scope [B (),F "y",F "z"]
abstract1 :: (Monad f, Eq a) => a -> f a -> Scope () f a
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
  F a -> a
{-# INLINE instantiate #-}

-- | Enter a 'Scope' that binds one variable, instantiating it
--
-- >>> instantiate1 "x" $ Scope [B (),F "y",F "z"]
-- "xyz"
instantiate1 :: Monad f => f a -> Scope n f a -> f a
instantiate1 e = instantiate (const e)
{-# INLINE instantiate1 #-}

-------------------------------------------------------------------------------
-- Traditional de Bruijn
-------------------------------------------------------------------------------

-- | @'fromScope'@ quotients out the possible placements of 'F' in 'Scope'
-- by distributing them all to the leaves. This yields a more traditional
-- de Bruijn indexing scheme for bound variables.
--
-- Since,
--
-- @'fromScope' '.' 'toScope' ≡ 'id'@
--
-- we know that
--
-- @'fromScope' '.' 'toScope' '.' 'fromScope' ≡ 'fromScope'@
--
-- and therefore @('toScope' . 'fromScope')@ is idempotent.
fromScope :: Monad f => Scope b f a -> f (Var b a)
fromScope (Scope s) = s >>= \v -> case v of
  F e -> fmap F e
  B b -> pure (B b)
{-# INLINE fromScope #-}

-- | Convert from traditional de Bruijn to generalized de Bruijn indices.
--
-- This requires a full tree traversal
toScope :: Monad f => f (Var b a) -> Scope b f a
toScope e = Scope (fmap (fmap pure) e)
{-# INLINE toScope #-}

-------------------------------------------------------------------------------
-- Exotic Traversals of Bound Variables (not exported by default)
-------------------------------------------------------------------------------

-- | Perform substitution on both bound and free variables in a 'Scope'.
splat :: Monad f => (a -> f c) -> (b -> f c) -> Scope b f a -> f c
splat f unbind s = unscope s >>= \v -> case v of
  B b -> unbind b
  F ea -> ea >>= f
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
mapScope f g (Scope s) = Scope $ fmap (bimap f (fmap g)) s
{-# INLINE mapScope #-}

-- | Obtain a result by collecting information from bound variables
foldMapBound :: (Foldable f, Monoid r) => (b -> r) -> Scope b f a -> r
foldMapBound f (Scope s) = foldMap f' s where
  f' (B a) = f a
  f' _     = mempty
{-# INLINE foldMapBound #-}

-- | Obtain a result by collecting information from both bound and free
-- variables
foldMapScope :: (Foldable f, Monoid r) =>
                (b -> r) -> (a -> r) -> Scope b f a -> r
foldMapScope f g (Scope s) = foldMap (bifoldMap f (foldMap g)) s
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
traverseScope_ f g (Scope s) = traverse_ (bitraverse_ f (traverse_ g)) s
{-# INLINE traverseScope_ #-}

-- | 'traverse' the bound variables in a 'Scope'.
traverseBound :: (Applicative g, Traversable f) =>
                 (b -> g c) -> Scope b f a -> g (Scope c f a)
traverseBound f (Scope s) = Scope <$> traverse f' s where
  f' (B b) = B <$> f b
  f' (F a) = pure (F a)
{-# INLINE traverseBound #-}

-- | Traverse both bound and free variables
traverseScope :: (Applicative g, Traversable f) =>
                 (b -> g d) -> (a -> g c) -> Scope b f a -> g (Scope d f c)
traverseScope f g (Scope s) = Scope <$> traverse (bitraverse f (traverse g)) s
{-# INLINE traverseScope #-}

-- | This allows you to 'bitraverse' a 'Scope'.
bitraverseScope :: (Bitraversable t, Applicative f) => (k -> f k') -> (a -> f a') -> Scope b (t k) a -> f (Scope b (t k') a')
bitraverseScope f = bitransverseScope (bitraverse f)
{-# INLINE bitraverseScope #-}

-- | This is a higher-order analogue of 'traverse'.
transverseScope :: (Applicative f, Monad f, Traversable g)
                => (forall r. g r -> f (h r))
                -> Scope b g a -> f (Scope b h a)
transverseScope tau (Scope e) = Scope <$> (tau =<< traverse (traverse tau) e)

bitransverseScope :: Applicative f => (forall a a'. (a -> f a') -> t a -> f (u a')) -> (c -> f c') -> Scope b t c -> f (Scope b u c')
bitransverseScope tau f = fmap Scope . tau (_F (tau f)) . unscope
{-# INLINE bitransverseScope #-}

-- | instantiate bound variables using a list of new variables
instantiateVars :: Monad t => [a] -> Scope Int t a -> t a
instantiateVars as = instantiate (vs !!) where
  vs = map pure as
{-# INLINE instantiateVars #-}

-- | Lift a natural transformation from @f@ to @g@ into one between scopes.
hoistScope :: Functor f => (forall x. f x -> g x) -> Scope b f a -> Scope b g a
hoistScope t (Scope b) = Scope $ t (fmap t <$> b)
{-# INLINE hoistScope #-}

instance (Binary b, Binary (f (Var b (f a))), Binary a) => Binary (Scope b f a)
instance (NFData b, NFData (f (Var b (f a))), NFData a) => NFData (Scope b f a)
