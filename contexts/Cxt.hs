{-# LANGUAGE DataKinds, TypeOperators, MultiParamTypeClasses, TypeFamilies, GADTs, ScopedTypeVariables, RankNTypes #-}
module Cxt where

-- This module plays with explicit context representations of fully typed terms.
-- The terms have both hoas and nested debruijn binding forms, which may be mixed freely.
-- closed terms form a restricted monad, and open terms a module over that monad.
-- abst . interp (aka reduce) gives normalization by evaluation for closed terms
-- and normalize gives normalization for open terms.

-- ideas include extending this to handle e.g. region effects or linear structures in the context
-- or to handling typeclasses or other structures in the context.

-- also, we can attempt to look at the relationship between the hoas and debruijn formulations
-- and demonstrate their equivalence via yoneda.

-- finally, we can try to turn our contexts into "telescopes" and capture dependent type theory.

data Type = TyPair Type Type | TyInt | TyArr Type Type

type family Repr t where
   Repr TyInt = Int
   Repr (TyPair a b) = (Repr a, Repr b)
   Repr (TyArr  a b) = Repr a -> Repr b

data Cxt = CCons Type Cxt | CNil

data Term cxt a where
-- common elements
   TmPure :: Repr a -> Term cxt a
   App    :: Term cxt (TyArr a b) -> Term cxt a -> Term cxt b

-- hoas
   Lam    :: (Term cxt a -> Term cxt b) -> Term cxt (TyArr a b)

-- Nested syntax formulation
   Var    :: Term (CCons a cxt) a
   Abs    :: Term (CCons a cxt) b -> Term cxt (TyArr a b)
   Weaken :: Term cxt a -> Term (CCons b cxt) a

-- primitives
   TmPlus :: Term cxt TyInt -> Term cxt TyInt -> Term cxt TyInt

-- closed terms form a (restricted) monad
cpure :: Repr a -> Term CNil a
cpure = TmPure

cbind :: Term CNil a -> (Repr a -> Term CNil b) -> Term CNil b
cbind x f = App (Lam $ f . interp) x

abst :: Repr a -> Term cxt a
abst = TmPure

interp :: forall a. Term CNil a -> Repr a
interp (TmPure x) = x
interp (App f x) = (interp f) (interp x)
interp (TmPlus x y) = interp x + interp y
interp (Lam f) = interp . f . abst
interp (Abs body) = \x -> interp $ subst (abst x) body

-- open terms form a module over a monad, with subst as the action of the module.

subst :: Term cxt a -> Term (CCons a cxt) b -> Term cxt b
subst tm (TmPure x) = (TmPure x)
subst tm (App f x) = App (subst tm f) (subst tm x)
subst tm (TmPlus x y) = TmPlus (subst tm x) (subst tm y)
subst tm (Lam f) = Lam  (subst tm . f . Weaken)
subst tm Var = tm
subst tm (Abs body) = Abs (liftFunc (subst tm) Weaken body)
subst tm (Weaken x) = x

liftFunc:: (forall b. Term cxt1 b -> Term cxt b)
           -> (forall b. Term cxt b -> Term cxt1 b)
           -> (forall c. Term (CCons c cxt1) b -> Term (CCons c cxt) b)
liftFunc f i (TmPure x) = (TmPure x)
liftFunc f i (App x y) = App (liftFunc f i x) (liftFunc f i y)
liftFunc f i (TmPlus x y) = TmPlus (liftFunc f i x) (liftFunc f i y)
liftFunc f i (Weaken b) = Weaken (f b)
liftFunc f i (Abs b) = Abs ((liftFunc (liftFunc f i) (liftFunc i f)) b)
liftFunc f i (Lam g) = Lam (liftFunc f i . g . liftFunc i f)
liftFunc f i Var = Var

reduce :: Term CNil a -> Term CNil a
reduce x = abst . interp $ x

normalize :: Term cxt a -> Term cxt a
normalize (TmPure x) = (TmPure x)
normalize Var = Var
normalize (Abs b) = Abs (normalize b)
normalize (Weaken b) = Weaken (normalize b)
normalize (Lam f) = (Lam f)
normalize (App x y) = case (normalize x, normalize y) of
   (TmPure x, TmPure y) -> TmPure $ x y
   (Abs b, x) -> normalize $ subst x b
   (Lam f, x) -> normalize $ f x
   (x,y) -> App x y
normalize (TmPlus x y) = case (normalize x, normalize y) of
  (TmPure x, TmPure y) -> TmPure $ x + y
  (x,y) -> TmPlus x y

tm_id :: Term CNil (TyArr TyInt TyInt)
tm_id = Lam $ \x -> x

tm_k :: Term CNil (TyArr TyInt (TyArr TyInt TyInt))
tm_k = Lam $ \x -> Lam $ \_y -> x

tm_flip :: Term CNil (TyArr (TyArr a (TyArr b c)) (TyArr b (TyArr a c)))
tm_flip = Lam $ \f -> Lam $ \x -> Lam $ \y -> App (App f y) x

tm_s :: Term CNil (TyArr (TyArr TyInt (TyArr TyInt TyInt)) (TyArr (TyArr TyInt TyInt) (TyArr TyInt TyInt)))
tm_s = Lam $ \f -> Lam $ \g -> Lam $ \x ->
           App
             (App f x)
             (App g x)

tm_id2 :: Term CNil (TyArr TyInt TyInt)
tm_id2 = Abs Var

tm_k2 :: Term CNil (TyArr TyInt (TyArr TyInt TyInt))
tm_k2 = Abs (Abs (Weaken Var))

tm_flip2 :: Term CNil (TyArr (TyArr a (TyArr b c)) (TyArr b (TyArr a c)))
tm_flip2 = Abs (Abs (Abs (App (App (Weaken . Weaken $ Var) Var) (Weaken Var))))

tm_cons :: Term CNil (TyArr TyInt (TyArr TyInt (TyPair TyInt TyInt)))
tm_cons = Lam $ \x -> Lam $ \y -> TmPure (interp x, interp y)

tm_fst :: Term CNil (TyArr (TyPair TyInt TyInt) TyInt)
tm_fst = Lam $ \x -> case interp x of (a,b) -> TmPure a

tm_eta_fst = Abs (App (Weaken tm_fst) Var)

test = interp tm_s (*) (negate) 12

test2 = interp (App tm_s (App tm_flip tm_k)) (+5) 12

test3 = subst (Weaken (cpure 12 :: Term CNil TyInt)) (TmPlus Var (Weaken Var))

test4 = interp $ (App tm_fst (App (App tm_cons (TmPure 12)) (TmPure 22)))

test5 = interp tm_eta_fst (23,45)