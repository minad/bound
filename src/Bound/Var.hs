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
----------------------------------------------------------------------------
module Bound.Var
  ( Var(..)
  , unvar
  , _B
  , _F
  ) where

import Control.DeepSeq (NFData)
import Control.Monad (ap)
import Data.Bifunctor.TH
import Data.Binary (Binary)
import Data.Deriving
import Data.Hashable
import Data.Hashable.Lifted
import Data.Profunctor
import GHC.Generics

----------------------------------------------------------------------------
-- Bound and Free Variables
----------------------------------------------------------------------------

-- | \"I am not a number, I am a /free monad/!\"
--
-- A @'Var' b a@ is a variable that may either be \"bound\" ('B') or \"free\" ('F').
--
-- (It is also technically a free monad in the same near-trivial sense as
-- 'Either'.)
data Var b a
  = B b -- ^ this is a bound variable
  | F a -- ^ this is a free variable
  deriving (Eq, Ord, Show, Read, Generic, Generic1, Functor, Foldable, Traversable)

distinguisher :: Int
distinguisher = fromIntegral $ (maxBound :: Word) `quot` 3

instance Hashable2 Var where
  liftHashWithSalt2 h _ s (B b) = h s b
  liftHashWithSalt2 _ h s (F a) = h s a `hashWithSalt` distinguisher
  {-# INLINE liftHashWithSalt2 #-}

instance Hashable b => Hashable1 (Var b) where
  liftHashWithSalt = liftHashWithSalt2 hashWithSalt
  {-# INLINE liftHashWithSalt #-}

instance (Hashable b, Hashable a) => Hashable (Var b a) where
  hashWithSalt s (B b) = hashWithSalt s b
  hashWithSalt s (F a) = hashWithSalt s a `hashWithSalt` distinguisher
  {-# INLINE hashWithSalt #-}

instance (Binary b, Binary a) => Binary (Var b a)
instance (NFData b, NFData a) => NFData (Var b a)

unvar :: (b -> r) -> (a -> r) -> Var b a -> r
unvar f _ (B b) = f b
unvar _ g (F a) = g a
{-# INLINE unvar #-}

-- |
-- This provides a @Prism@ that can be used with @lens@ library to access a bound 'Var'.
--
-- @
-- '_B' :: 'Prism' (Var b a) (Var b' a) b b'@
-- @
_B :: (Choice p, Applicative f) => p b (f b') -> p (Var b a) (f (Var b' a))
_B = dimap (unvar Right (Left . F)) (either pure (fmap B)) . right'
{-# INLINE _B #-}

-- |
-- This provides a @Prism@ that can be used with @lens@ library to access a free 'Var'.
--
-- @
-- '_F' :: 'Prism' (Var b a) (Var b a') a a'@
-- @
_F :: (Choice p, Applicative f) => p a (f a') -> p (Var b a) (f (Var b a'))
_F = dimap (unvar (Left . B) Right) (either pure (fmap F)) . right'
{-# INLINE _F #-}

----------------------------------------------------------------------------
-- Instances
----------------------------------------------------------------------------

instance Applicative (Var b) where
  pure = F
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Var b) where
  F a >>= f = f a
  B b >>= _ = B b
  {-# INLINE (>>=) #-}

deriveBifunctor ''Var
deriveBifoldable ''Var
deriveBitraversable ''Var
deriveEq1 ''Var
deriveEq2 ''Var
deriveOrd1 ''Var
deriveOrd2 ''Var
deriveShow1 ''Var
deriveShow2 ''Var
deriveRead1 ''Var
deriveRead2 ''Var
