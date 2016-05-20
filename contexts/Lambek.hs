{-# LANGUAGE DataKinds, TypeOperators, MultiParamTypeClasses, TypeFamilies, GADTs, ScopedTypeVariables, RankNTypes, PolyKinds, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}

module Lambek(
) where
import Prelude hiding ((.))
import Control.Category as C

import Debug.Trace
import System.IO.Unsafe
import Control.Concurrent

{-
Explorations in lambda terms as elements of presheaves, or generally as slices in a category of contexts.
-}

-- We begin with objects of cartesian closed categories over some base index of types.
data TCart b = TUnit | TPair (TCart b) (TCart b) | TExp (TCart b) (TCart b) | TBase b

-- Base indices are mapped to types via Repr
type family Repr a :: *

-- Cartesian objects over the base are mapped to types via CartRepr
type family CartRepr a :: *

-- Ty is used to wrap polykinded things up in kind *
data Ty a

type instance CartRepr (Ty (TBase a)) = Repr (Ty a)
type instance CartRepr (Ty (TPair a b)) = (CartRepr (Ty a), CartRepr (Ty b))
type instance CartRepr (Ty (TExp a b))  = CartRepr (Ty a) -> CartRepr (Ty b)
type instance CartRepr (Ty TUnit) = ()

data ABase = AInt | AString | ADouble

type instance Repr (Ty AInt) = Int
type instance Repr (Ty AString) = String
type instance Repr (Ty ADouble) = Double


-- A Context b is a list of cartesian objects over base index b
data Cxt b = CCons (TCart b) (Cxt b) | CNil


-- We define a category of contexts by providing the morphisms as a GADT
-- These morphisms can also be read in logical terms:
--
-- CxtArr a b is a judgment a |- b
-- when b contains multiple terms this is a sequent
--
-- CxtArr a b -> CxtArr c d is an inference rule
--   a |- b
-- ---------
--   c |- d

-- This category also can be read topologically as having a simplicial structure induced by face and degeneracy maps.

data CxtArr :: Cxt a -> Cxt a -> *  where
  -- To be a category we must have id and composition
  CXAId  :: CxtArr a a
  CXACompose :: CxtArr b c -> CxtArr a b -> CxtArr a c

  -- We have a terminal object
  CXANil :: CxtArr a CNil

  -- We have face maps
  CXAWeaken :: CxtArr (CCons a cxt) cxt

  -- We have degeneracy maps
  CXADiag :: CxtArr (CCons a cxt) (CCons a (CCons a cxt))

  -- We have additional "degeneracy" maps given by every inhabitant of our underlying terms
  CXAAtom :: CartRepr (Ty a) -> CxtArr cxt (CCons a cxt)

  -- We also have a cartesian structure
  CXAPair  :: CxtArr cxt (CCons a c2) -> CxtArr cxt (CCons b c2) -> CxtArr cxt (CCons (TPair a b) c2)
  CXAPairProj1 :: CxtArr (CCons (TPair a b) cxt) (CCons a cxt)
  CXAPairProj2 :: CxtArr (CCons (TPair a b) cxt) (CCons b cxt)

  -- And a closed structure (aka uncurry and eval)
  CXAEval  :: CxtArr (CCons (TPair (TExp a b) a) cxt) (CCons b cxt)
  CXAAbs   :: CxtArr (CCons a cxt) (CCons b c) -> CxtArr cxt (CCons (TExp a b) c)

  -- We also add directly the internal hom in a slice category, which _also_ should give a closed structure.
  CXALam   :: (forall c. CxtArr c cxt -> CxtArr c (CCons a c2) -> CxtArr c (CCons b c2)) -> CxtArr cxt (CCons (TExp a b) c2)

  -- Todo, some functoriality of contextual operations? i.e. context morphisms should be stable under extension.

-- A Hacky Show Instance
instance Show (CxtArr a b) where
    show CXAId = "CXAId"
    show (CXACompose g f) = show g ++ " . " ++ show f
    show CXANil = "CXANil"
    show (CXAAtom x) = "CXAAtom"
    show CXAWeaken = "CXAWeaken"
    show CXAEval = "CXAEval"
    show (CXALam f) = "CXALam"
    show (CXAAbs f) = "CXAAbs (" ++ show f ++ ")"
    show (CXAPair f g) = "(" ++ show f ++ ", " ++ show g ++ ")"
    show CXAPairProj1 = "CXAPairProj1"
    show CXAPairProj2 = "CXAPairProj2"
    show CXADiag = "CXADiag"

-- We give axioms on our category as conditions on coherence of composition
-- As per section 10 of  http://arxiv.org/pdf/math/9911073.pdf
cxaCompose :: CxtArr b c -> CxtArr a b -> CxtArr a c
cxaCompose CXAId f = f
cxaCompose f CXAId = f
cxaCompose CXANil _ = CXANil
cxaCompose CXAEval (CXAPair (CXALam f) g) = f CXAId g
cxaCompose CXAPairProj1 (CXAPair a b) = a
cxaCompose CXAPairProj2 (CXAPair a b) = b

-- TODO: further rules for weaken or diag, in interaction with eval in particular?
cxaCompose CXAWeaken CXADiag = CXAId

cxaCompose h (CXACompose g f) = CXACompose (cxaCompose h g) f

-- with this we can get stuck. ideally we'll never hit it.
cxaCompose f g = CXACompose f g


-- CxtArr indeed gives a category
instance Category CxtArr where
    id = CXAId
    (.) = cxaCompose

-- Terms here are elements or fibers of presheaves. Alternately, terms of type A are elements of the slice category over the context containing only A.
-- That is, a term is a sequent judgment which corresponds to a natural judgement (has only one consequent).
data Term cxt a where
    Term :: CxtArr cxt (CCons a CNil) -> Term cxt a
-- An experiment in progress
--    LamTerm :: (forall c. CxtArr c cxt -> CxtArr c (CCons d cxt) -> CxtArr c (CCons b cxt)) -> Term cxt (TExp d b)

instance Show (Term cxt a) where
    show (Term x) = show x
--    show (LamTerm f) = "LamTerm"

unTerm :: Term cxt a -> CxtArr cxt (CCons a CNil)
unTerm (Term x) = x
-- unTerm (LamTerm f) = CXAAbs (f CXAWeaken _)

-- We can now write lam, app etc over terms just as we would in a typical embedding

lamTerm :: (forall c. CxtArr c cxt -> Term c a -> Term c b) -> Term cxt (TExp a b)
--lamTerm f = LamTerm (\m x -> unTerm (f m (Term x)))
lamTerm f = Term (CXALam (\m x -> unTerm (f m (Term x))))

appTerm :: Term cxt (TExp a b) -> Term cxt a -> Term cxt b
appTerm f x = Term (CXAEval . (CXAPair (unTerm f) (unTerm x)))

-- in the slice, weaken gives the inverse image along a face
weakenTerm :: Term cxt a -> Term (CCons b cxt) a
weakenTerm = Term . (. CXAWeaken) . unTerm

-- and abs gives a form of inverse image along a degeneracy?
absTerm :: Term (CCons a cxt) b -> Term cxt (TExp a b)
absTerm = Term . CXAAbs . unTerm

liftTerm :: Term CNil a -> Term cxt a
liftTerm = Term . (. CXANil) . unTerm

contractTerm :: Term (CCons a (CCons a cxt)) b  -> Term (CCons a cxt) b
contractTerm = Term . (. CXADiag) . unTerm

varTerm :: Term (CCons a CNil) a
varTerm = Term CXAId

appArrow :: CxtArr c d -> Term d a -> Term c a
appArrow h (Term g) = Term $ g . h


-- Abstraction (in the sense of nbe) is a free operation
abst :: CartRepr (Ty a) -> Term CNil a
abst = Term . CXAAtom

-- Interpretation does the obvious thing
interp' :: Term CNil a -> CartRepr (Ty a)
interp' (Term (CXAAtom x)) = x
interp' (Term (CXAPair f g)) = (interp (Term f), interp (Term g))
interp' (Term (CXALam f)) = interp . Term . f CXAId . unTerm . abst
interp' (Term (CXAAbs f)) = interp (Term (CXALam $ \_ x -> f . x))

--Again we should never need explicit composition
--interp' (Term (CXACompose f g)) =  interp (Term (f . g))

-- Here again is a partial experiment
--interp' (LamTerm f) = interp . Term . f CXAId . CXAAtom
--interp' (Term (CXAAbs f)) = interp (LamTerm $ \_ x -> f . x)

-- Here we wrap interpretation for tracing evaluation
interp :: Term CNil a -> CartRepr (Ty a)
interp x = unsafePerformIO (threadDelay 100000) `seq` traceShow x (interp' x)

-- And nbe does what we want
nbe :: Term CNil a -> Term CNil a
nbe = abst . interp

subst :: Term (CCons a cxt) t -> Term cxt a -> Term cxt t
subst = appTerm . absTerm

-- Substitution gives a module over a relative monad
runit :: Term cxt a -> Term (CCons b cxt) a
runit = weakenTerm

rmap :: Term cxt (TExp a b) -> Term cxt a -> Term cxt b
rmap = appTerm

rjoin :: Term (CCons b (CCons b cxt)) a -> Term (CCons b cxt) a
rjoin = contractTerm


-- To be done, explore if LamTerm gives proper derivability vs. admissibility rule
-- Todo -- see if we want to distinguish the simplicial structure of contexts from the value stucture?


-- Some examples
tmInt :: Int -> Term CNil (TBase AInt)
tmInt i = Term (CXAAtom i)

lam :: (forall c. Term c a -> Term c b) -> Term cxt (TExp a b)
lam f = lamTerm $ \ h -> f

lamt :: (forall c. CxtArr c cxt -> Term c a -> Term c b) -> Term cxt (TExp a b)
lamt f = lamTerm f

tm_id = lam $ \x -> x

tm_id2 = Term (CXAAbs CXAId)

tm_k = lam $ \x -> lamTerm $ \g y -> appArrow g x

tm_s = lamt $ \h f -> lamt $ \h1 g -> lamt $ \h2 x -> appTerm (appTerm (appArrow (h1 . h2) f) x) (appTerm (appArrow h2 g) x)

tm_comp :: Term cxt (TExp (TExp a1 b) (TExp (TExp a a1) (TExp a b)))
tm_comp = lamt $ \h f -> lamt $ \h1 g -> lamt $ \h2 x -> appTerm (appArrow (h1 . h2) f) (appTerm (appArrow h2 g) x)

tm_f :: Term CNil (TExp (TExp a b) (TExp a a))
tm_f = appTerm tm_s tm_k


-- Testing the interpreter
test = (interp (tm_id :: Term cxt (TExp (TBase AInt) (TBase AInt)))) $ 12
test2 = (interp (tm_id2 :: Term CNil (TExp (TBase AInt) (TBase AInt)))) $ 12

itm_f :: (Double -> String) -> (Double -> Double)
itm_f = interp (tm_f :: Term CNil (TExp (TExp (TBase ADouble) (TBase AString)) (TExp (TBase ADouble) (TBase ADouble)))) -- necessary because we don't have injective type families

-- The above structure can perhaps be treated perhaps as a Category with Attributes where we don't have "real" contexts, but instead can "push" all our contexts [a,b,c] |- d into Nil |- (a,b,c) -> d, as the types don't depend on elements of the context. Introduction of genuine Pi types should screw this possibility up in interesting ways.