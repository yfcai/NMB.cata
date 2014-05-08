{-# LANGUAGE RankNTypes, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

import Data.Typeable

gencom = C [D "Research" ralf [PU joost, PU marlow], D "Strategy" blair []]

ralf = E (P "Ralf" "Amsterdam") (S 8000)
joost = E (P "Joost" "Amsterdam") (S 1000)
marlow = E (P "Marlow" "Cambridge") (S 2000)
blair = E (P "Blair" "London") (S 100000)

incS :: Float -> Salary -> Salary
incS k (S s) = S (s * (1 + k))

-- if type is correct, then transform, else apply identity
mkT :: (Typeable a, Typeable b) => (b -> b) -> a -> a
mkT f = case cast f of Just g -> g ; Nothing -> id
-- can't write `withDefault id` due to type checker's lack of insight

mkQ :: (Typeable a, Typeable b) => r -> (b -> r) -> a -> r
mkQ r = withDefault (const r)

-- if type is correct, then transform, else provide default
withDefault :: (Typeable a, Typeable b) => (a -> r) -> (b -> r) -> (a -> r)
withDefault old new a = case cast a of Just b -> new b ; Nothing -> old a

-- mapping over an n-nary function without caring so much about types
-- the functor is hidden. which is good.
-- Term a means a is the result of an n-nary functor.
-- There's no guarantee gmapT'd be correct.
-- This covers the important use case of type-invariant transformation.
-- Context = Hole in this case.
class Typeable a => Term a where
  gmapT :: (forall b. Term b => (b -> b)) -> a -> a
  gmapT f x = let k c x = ID (unID c (f x)) in unID (gfoldl k ID x)

  gfoldl :: (forall a b. Term a => w (a -> b) -> a -> w b)
         -> (forall g. g -> w g)
         -> a -> w a
  gfoldl k z a = z a

-- boilerplate
newtype ID x = ID { unID :: x }

instance Term Float
instance Term Char -- for String

instance Term a => Term [a] where
  gfoldl k z [] = z []
  gfoldl k z (x : xs) = k (k (z (:)) x) xs

data Company = C [Dept] deriving (Typeable, Show)
data Dept = D Name Manager [SubUnit] deriving (Typeable, Show)
data SubUnit = PU Employee | DU Dept deriving (Typeable, Show)
data Employee = E Person Salary deriving (Typeable, Show)
data Person = P Name Address deriving (Typeable, Show)
data Salary = S Float deriving (Typeable, Show)
type Manager = Employee
type Name = String
type Address = String

instance Term Salary where gfoldl k z (S s) = k (z S) s
instance Term Person where gfoldl k z (P n a) = k (k (z P) n) a
instance Term Employee where gfoldl k z (E p s) = k (k (z E) p) s
instance Term SubUnit where gfoldl k z u = case u of PU e -> k (z PU) e ; DU d -> k (z DU) d
instance Term Dept where gfoldl k z (D n m us) = k (k (k (z D) n) m) us
instance Term Company where gfoldl k z (C ds) = k (z C) ds

-- is there any type safety to speak of here?
-- `everywhere` can be called on everything!
everywhere :: (Term a, Typeable b) => (b -> b) -> (a -> a)
everywhere f x = mkT f (gmapT (everywhere f) x)

incC :: Float -> Company -> Company
incC k = everywhere (incS k)
