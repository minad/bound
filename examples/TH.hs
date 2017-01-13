{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
module TH where

import Bound
import Data.Deriving

infixl 9 :@

data Exp a
  = V a
  | Exp a :@ Exp a
  | Lam (Scope () Exp a)
  | ND [Exp a]
  | I Int
  deriving (Functor, Foldable, Traversable)

deriveEq1   ''Exp
deriveShow1 ''Exp
makeBound   ''Exp

deriving instance Eq a => Eq (Exp a)
deriving instance Show a => Show (Exp a)

-- |
-- >>> lam 'x' (V 'x') :@ V 'y'
-- Lam (Scope (V (B ()))) :@ V 'y'
lam :: Eq a => a -> Exp a -> Exp a
lam v b = Lam (abstract1 v b)

-- |
-- >>> whnf $ lam 'x' (V 'x') :@ V 'y'
-- V 'y'
whnf :: Exp a -> Exp a
whnf (f :@ a) = case whnf f of
  Lam b -> whnf (instantiate1 a b)
  f'    -> f' :@ a
whnf e = e

main :: IO ()
main = pure ()
