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

data Type = TyPair Type Type | TyInt | TyArr Type Type | TyUnit

data Void

type family Repr t where
   Repr TyInt = Int
   Repr (TyPair a b) = (Repr a, Repr b)
   Repr (TyArr  a b) = Repr a -> Repr b
   Repr TyUnit = ()

data Cxt = CCons Type Cxt | CNil

data Term cxt a where
-- common elements
   TmPure :: Repr a -> Term cxt a
   App    :: Term cxt (TyArr a b) -> Term cxt a -> Term cxt b

-- hoas

-- Lam represents _admissible_ terms, which includes "exotic" ones only definable in the metalogic.
   Lam    :: (Term cxt a -> Term cxt b) -> Term cxt (TyArr a b)

-- PLam internalizes parametricity and only represents _derivable_ terms -- ones that are admissiable in any extension of the context. These correspond to terms that are derivable directly in the target language.
   PLam   :: (forall c. Term (CCons c cxt) a -> Term (CCons c cxt) b) -> Term cxt (TyArr a b)

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

-- mapCxt witnesses that context are (pro)functorial with regards to weakening
mapCxt:: (forall b. Term cxt1 b -> Term cxt b)
      -> (forall b. Term cxt  b -> Term cxt1 b)
      -> (forall c. Term (CCons c cxt1) b -> Term (CCons c cxt) b)
mapCxt f i (TmPure x) = (TmPure x)
mapCxt f i (App x y) = App (mapCxt f i x) (mapCxt f i y)
mapCxt f i (TmPlus x y) = TmPlus (mapCxt f i x) (mapCxt f i y)
mapCxt f i (Weaken b) = Weaken (f b)
mapCxt f i (Abs b) = Abs ((mapCxt (mapCxt f i) (mapCxt i f)) b)
mapCxt f i (Lam g) = Lam (mapCxt f i . g . mapCxt i f)
mapCxt f i (PLam g) = PLam (mapCxt (mapCxt f i) (mapCxt i f)
                          . g
                          . mapCxt (mapCxt i f) (mapCxt f i))
mapCxt f i Var = Var

-- abst sends host terms to embedded terms, and interp interprets embedded terms, in the empty context, to host terms in an entirely type safe way.
abst :: Repr a -> Term cxt a
abst = TmPure

interp :: forall a. Term CNil a -> Repr a
interp (TmPure x) = x
interp (App f x) = (interp f) (interp x)
interp (TmPlus x y) = interp x + interp y
interp (Lam f) = interp . f . abst
interp (PLam f) = interp . contractCxt . f . abst
interp (Abs body) = \x -> interp $ subst (abst x) body


-- Interpretation of parametric terms proceeds by taking their results, which are derivable in any context, and instantiating them to our specific context, by chosing the context extension to be Unit, and the contracting away the unit.
contractCxt :: Term (CCons TyUnit cxt) a -> Term cxt a
contractCxt (TmPure x) = TmPure x
contractCxt (App f x) = App (contractCxt f) (contractCxt x)
contractCxt (TmPlus x y) = TmPlus (contractCxt x) (contractCxt y)
contractCxt (Lam f) = Lam (contractCxt . f . Weaken)
contractCxt Var = TmPure ()
contractCxt (Weaken x) = x
contractCxt (Abs b) = Abs (mapCxt contractCxt Weaken b)
contractCxt (PLam f) = PLam (mapCxt contractCxt Weaken . f . mapCxt Weaken contractCxt)

-- open terms form a module over a monad, with subst as the action of the module.
subst :: Term cxt a -> Term (CCons a cxt) b -> Term cxt b
subst tm (TmPure x) = (TmPure x)
subst tm (App f x) = App (subst tm f) (subst tm x)
subst tm (TmPlus x y) = TmPlus (subst tm x) (subst tm y)
subst tm (Lam f) = Lam  (subst tm . f . Weaken)
subst tm (PLam f) = PLam (mapCxt (subst tm) Weaken . f . mapCxt Weaken (subst tm))
subst tm Var = tm
subst tm (Abs body) = Abs (mapCxt (subst tm) Weaken body)
subst tm (Weaken x) = x

-- abst and interp provide normalization by evaluation in the empty context.
reduce :: Term CNil a -> Term CNil a
reduce x = abst . interp $ x

-- Normalize brings open terms to whnf.
-- Other strategies are possible based on the choice of _when_ to evaluate _what_ in the case of application.
normalize :: Term cxt a -> Term cxt a
normalize (TmPure x) = (TmPure x)
normalize Var = Var
normalize (Abs b) = Abs (normalize b)
normalize (Weaken b) = Weaken (normalize b)
normalize (Lam f) = (Lam f)
normalize (PLam f) = (PLam f)
normalize (App x y) = case (normalize x, normalize y) of
   (TmPure x, TmPure y) -> TmPure $ x y
   (Abs b, x)  -> normalize $ subst x b
   (Lam f, x)  -> normalize $ f x
   (PLam f, x) -> normalize . contractCxt $ f (Weaken x)
   (x,y) -> App x y
normalize (TmPlus x y) = case (normalize x, normalize y) of
  (TmPure x, TmPure y) -> TmPure $ x + y
  (x,y) -> TmPlus x y


-- We can sort of go from hoas to debruijn and back as per atkey, lindley, yallop: http://bentnib.org/unembedding.html
-- relevant cases sketched below.
-- note that PLam makes hoas2db easy, but going from db to hoas via PLam is subtle.

db2hoas :: Term cxt a -> Term cxt a
db2hoas (Abs b) = Lam $ \x -> subst x b
-- challenge : write this with PLam.
-- this doesn't quite work: PLam $ \x -> subst x (mapCxt Weaken _ b)

hoas2db :: Term cxt a -> Term cxt a
hoas2db (PLam f) = Abs $ f Var
-- note that this appropriately doesn't work with Lam proper, since it is "too big"

-- This all should be relatable to yoneda.

-- examples


tm_id :: Term CNil (TyArr TyInt TyInt)
tm_id = Lam $ \x -> x

tm_pid :: Term CNil (TyArr TyInt TyInt)
tm_pid = PLam $ \x -> x

tm_polyid :: Term CNil (TyArr a TyInt)
tm_polyid = PLam $ \x -> (TmPure 12)

tm_admissible :: Term CNil (TyArr TyInt TyInt)
tm_admissible = Lam $ \x -> (abst . (+1) . interp) x

{-
Can't write this with PLam.
tm_not_derivable :: Term CNil (TyArr TyInt TyInt)
tm_not_derivable = PLam $ \x -> abst . (+1) $ interp (contractCxt x)
-}

tm_k :: Term CNil (TyArr TyInt (TyArr TyInt TyInt))
tm_k = Lam $ \x -> Lam $ \_y -> x

tm_pk :: Term CNil (TyArr TyInt (TyArr TyInt TyInt))
tm_pk = PLam $ \x -> Lam $ \_y -> x

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

test2 = interp (App tm_s (App tm_flip tm_pk)) (+5) 12

test3 = subst (Weaken (cpure 12 :: Term CNil TyInt)) (TmPlus Var (Weaken Var))

test4 = interp $ (App tm_fst (App (App tm_cons (TmPure 12)) (TmPure 22)))

test5 = interp tm_eta_fst (23,45)
