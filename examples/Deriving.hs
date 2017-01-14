{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
module Deriving where

import Data.List
import Control.Monad
import Data.Functor.Classes
import Bound
import Data.Deriving

infixl 9 :@

data Exp a
  = V a
  | Exp a :@ Exp a
  | Lam {-# UNPACK #-} !Int (Pat Exp a) (Scope Int Exp a)
  | Let {-# UNPACK #-} !Int [Scope Int Exp a] (Scope Int Exp a)
  | Case (Exp a) [Alt Exp a]
  deriving (Functor,Foldable,Traversable)

data Alt f a = Alt {-# UNPACK #-} !Int (Pat f a) (Scope Int f a)
  deriving (Eq,Show,Functor,Foldable,Traversable)

data Pat f a
  = VarP
  | WildP
  | AsP (Pat f a)
  | ConP String [Pat f a]
  | ViewP (Scope Int f a) (Pat f a)
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable)

instance Applicative Exp where
  pure = V
  (<*>) = ap

instance Monad Exp where
  V a        >>= f = f a
  (x :@ y)   >>= f = (x >>= f) :@ (y >>= f)
  Lam n p e  >>= f = Lam n (p >>>= f) (e >>>= f)
  Let n bs e >>= f = Let n (map (>>>= f) bs) (e >>>= f)
  Case e as  >>= f = Case (e >>= f) (map (>>>= f) as)

instance Bound Pat where
  VarP      >>>= _ = VarP
  WildP     >>>= _ = WildP
  AsP p     >>>= f = AsP (p >>>= f)
  ConP g ps >>>= f = ConP g (map (>>>= f) ps)
  ViewP e p >>>= f = ViewP (e >>>= f) (p >>>= f)

deriveShow1 ''Exp
deriveShow1 ''Pat
deriveShow1 ''Alt
deriveEq1   ''Exp

instance (Eq1 f, Monad f) => Eq1 (Pat f) where
  liftEq = $(makeLiftEq ''Pat)

instance (Eq1 f, Monad f) => Eq1 (Alt f) where
  liftEq = $(makeLiftEq ''Alt)

deriving instance Eq a => Eq (Exp a)
deriving instance Show a => Show (Exp a)

instance Bound Alt where
  Alt n p b >>>= f = Alt n (p >>>= f) (b >>>= f)

-- ** smart patterns

data P a = P { pattern :: [a] -> Pat Exp a, bindings :: [a] }

-- |
-- >>> lam (varp "x") (V "x")
-- Lam 1 VarP (Scope (V (B 0)))
varp :: a -> P a
varp a = P (const VarP) [a]

wildp :: P a
wildp = P (const WildP) []

asp :: a -> P a -> P a
asp a (P p as) = P (\bs -> AsP (p (a:bs))) (a:as)

-- |
-- >>> lam (conp "Hello" [varp "x", wildp]) (V "y")
-- Lam 1 (ConP "Hello" [VarP,WildP]) (Scope (V (F (V "y"))))
conp :: String -> [P a] -> P a
conp g ps = P (ConP g . go ps) (ps >>= bindings)
  where
    go (P p as:ps') bs = p bs : go ps' (bs ++ as)
    go [] _ = []

-- | view patterns can view variables that are bound earlier than them in the pattern
viewp :: Eq a => Exp a -> P a -> P a
viewp t (P p as) = P (\bs -> ViewP (abstract (`elemIndex` bs) t) (p bs)) as

-- | smart lam constructor
--
-- >>> let_ [("x",V "y"),("y",V "x" :@ V "y")] $ lam (varp "z") (V "z" :@ V "y")
-- Let 2 [Scope (V (B 1)),Scope (V (B 0) :@ V (B 1))] (Scope (Lam 1 VarP (Scope (V (B 0) :@ V (F (V (B 1)))))))
--
-- >>> lam (conp "F" [varp "x", viewp (V "x") $ varp "y"]) (V "y")
-- Lam 2 (ConP "F" [VarP,ViewP (Scope (V (B 0))) VarP]) (Scope (V (B 1)))
--
-- >>> lam (conp "F" [varp "x", viewp (V "y") $ varp "y"]) (V "y")
-- Lam 2 (ConP "F" [VarP,ViewP (Scope (V (F (V "y")))) VarP]) (Scope (V (B 1)))
lam :: Eq a => P a -> Exp a -> Exp a
lam (P p as) t = Lam (length as) (p []) (abstract (`elemIndex` as) t)

-- | smart let constructor
let_ :: Eq a => [(a, Exp a)] -> Exp a -> Exp a
let_ bs b = Let (length bs) (map (abstr . snd) bs) (abstr b)
  where vs  = map fst bs
        abstr = abstract (`elemIndex` vs)

-- | smart alt constructor
--
-- >>> lam (varp "x") $ Case (V "x") [alt (conp "Hello" [varp "z",wildp]) (V "x"), alt (varp "y") (V "y")]
-- Lam 1 VarP (Scope (Case (V (B 0)) [Alt 1 (ConP "Hello" [VarP,WildP]) (Scope (V (F (V (B 0))))),Alt 1 VarP (Scope (V (B 0)))]))
alt :: Eq a => P a -> Exp a -> Alt Exp a
alt (P p as) t = Alt (length as) (p []) (abstract (`elemIndex` as) t)

main :: IO ()
main = pure ()
