{-# LANGUAGE DataKinds, TypeOperators, MultiParamTypeClasses, TypeFamilies, GADTs, ScopedTypeVariables, RankNTypes, PolyKinds, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}

module Lambek(
) where
import Prelude hiding ((.))
import Control.Category as C

{-
Explorations in lambda terms as elements of presheaves, or generally as slices in a category of contexts.
-}

data TCart b = TUnit | TPair (TCart b) (TCart b) | TExp (TCart b) (TCart b) | TBase b

type family Repr a :: *
type family CartRepr a :: *

data Ty a

type instance CartRepr (Ty (TBase a)) = Repr (Ty a)
type instance CartRepr (Ty (TPair a b)) = (CartRepr (Ty a), CartRepr (Ty b))
type instance CartRepr (Ty (TExp a b))  = CartRepr (Ty a) -> CartRepr (Ty b)
type instance CartRepr (Ty TUnit) = ()

data ABase = AInt | AString

type instance Repr (Ty AInt) = Int
type instance Repr (Ty AString) = String

data Cxt b = CCons (TCart b) (Cxt b) | CNil

-- CxtArr a b is an inference rule
--   a
-- -----
--   b

-- todo make simplicial? or make product of categories?

data CxtArr :: Cxt a -> Cxt a -> * where
  --category
  CXAId  :: CxtArr a a
  CXACompose :: CxtArr b c -> CxtArr a b -> CxtArr a c

  -- that has a terminal object
  CXANil :: CxtArr a CNil

  -- with degeneracy maps (atoms) given by closed terms
  CXAAtom :: CartRepr (Ty a) -> CxtArr cxt (CCons a cxt)

  -- and face maps given by projection
  CXAProj1 :: CxtArr (CCons a cxt) (CCons a CNil)
  CXAProj2 :: CxtArr (CCons a cxt) cxt

  -- with a cartesian structure
  CXAPair  :: CxtArr cxt (CCons a CNil) -> CxtArr cxt (CCons b CNil) -> CxtArr cxt (CCons (TPair a b) CNil)
  CXAPairProj1 :: CxtArr cxt (CCons (TPair a b) CNil) -> CxtArr cxt (CCons a CNil)
  CXAPairProj2 :: CxtArr cxt (CCons (TPair a b) CNil) -> CxtArr cxt (CCons b CNil)

  -- and a closed structure
  -- abst aka uncurry
  CXAAbst :: CxtArr (CCons a cxt) (CCons b CNil) -> CxtArr cxt (CCons (TExp a b) CNil)
  -- app aka eval
  CXAApp :: CxtArr cxt (CCons (TExp a b) CNil) -> CxtArr cxt (CCons a CNil) -> CxtArr cxt (CCons b CNil)

-- Todo add more coherences? normalization?
cxaCompose :: CxtArr b c -> CxtArr a b -> CxtArr a c
cxaCompose CXAId f = f
cxaCompose f CXAId = f
cxaCompose h (CXACompose g f) = cxaCompose (cxaCompose h g) f
cxaCompose g f = CXACompose g f

-- todo make instance of classes in categories lib?
instance Category CxtArr where
    id = CXAId
    (.) = cxaCompose

appTm :: Term cxt (TExp a b) -> Term cxt a -> Term cxt b
appTm f x = ConstTerm (CXAApp (unTerm f) (unTerm x))

unTerm :: Term cxt a -> CxtArr cxt (CCons a CNil)
unTerm (ConstTerm x) = x
unTerm (LamTerm f) = CXAAbst . unTerm $ (f CXAProj2 (ConstTerm CXAProj1))

appArrow :: CxtArr c d -> Term d a -> Term c a
appArrow h t = ConstTerm (unTerm t . h)

tm_mkpair2 :: Term cxt (TExp a (TExp b (TPair a b)))
tm_mkpair2 = lamt $ \h x -> lamt $ \g y -> ConstTerm (CXAPair (unTerm x . g) (unTerm y))

-- TODO: Add more constants?


-- terms here are slices over one element contexts, or exponentials.
-- TODO: Cata representation of terms?
data Term cxt a where
    ConstTerm :: CxtArr cxt (CCons a CNil) -> Term cxt a --representable
    LamTerm   :: (forall c. CxtArr c cxt -> Term c a -> Term c b) -> Term cxt (TExp a b)

lamt :: (forall c. CxtArr c cxt -> Term c a -> Term c b) -> Term cxt (TExp a b)
lamt f = ConstTerm . CXAAbst . unTerm $ (f CXAProj2 (ConstTerm CXAProj1))

--TODO can we write subst?
-- subst :: Term (CCons a cxt) t -> Term cxt a -> Term cxt t
-- subst = foo...



abst :: CartRepr (Ty a) -> Term CNil a
abst = ConstTerm . CXAAtom

interp :: Term CNil a -> CartRepr (Ty a)
interp (LamTerm f) = interp . f CXANil . abst
interp (ConstTerm f) = interpArr f

-- gah, gotta send contexts to concrete reprs, work wholemeal -- send cxtarrs to functions as a whole...

interpArr :: CxtArr CNil (CCons a CNil) -> CartRepr (Ty a)
interpArr (CXAAtom x) = x
interpArr (CXAPair x y) = (interpArr x, interpArr y)
interpArr (CXAPairProj1 x) = fst (interpArr x)
interpArr (CXAPairProj2 x) = snd (interpArr x)
interpArr (CXAAbst f) = \x -> interpArr (f . CXAAtom x)
interpArr (CXAApp f x) = (interpArr f) (interpArr x)
--interpArr (CXACompose CXAId f) = interpArr f
interpArr (CXACompose f CXANil) = interpArr f
interpArr (CXACompose f CXAId) = interpArr f
interpArr (CXACompose CXAId h@(CXAAtom g)) = undefined --interpArr (CXAAbst f) g
interpArr (CXACompose (CXAAtom f) g) = undefined
interpArr (CXACompose f (CXACompose g h)) = interpArr (CXACompose (CXACompose f g) h)
interpArr (CXACompose (CXACompose _ _) _) = error "welp"

tmInt :: Int -> Term CNil (TBase AInt)
tmInt i = ConstTerm (CXAAtom i)


weakenTerm :: Term cxt a -> Term (CCons b cxt) a
weakenTerm = appArrow CXAProj2

liftTm :: Term CNil a -> Term cxt a
liftTm = appArrow CXANil

varTm :: Term (CCons a CNil) a
varTm = ConstTerm CXAId

lam :: (forall c. Term c a -> Term c b) -> Term cxt (TExp a b)
lam f = lamt $ \h -> f
--lam f = LamTerm $ \ h -> f

tmid = ConstTerm (CXAAbst CXAId . CXANil)

tm_id = lam $ \x -> x

tm_k = lam $ \x -> LamTerm $ \g y -> appArrow g x

tm_s = lamt $ \h f -> lamt $ \h1 g -> lamt $ \h2 x -> appTm (appTm (appArrow (h1 . h2) f) x) (appTm (appArrow h2 g) x)

tm_comp :: Term cxt (TExp (TExp a1 b) (TExp (TExp a a1) (TExp a b)))
tm_comp = lamt $ \h f -> lamt $ \h1 g -> lamt $ \h2 x -> appTm (appArrow (h1 . h2) f) (appTm (appArrow h2 g) x)


{-
tm_mkpair :: Term cxt (TExp a (TExp b (TPair b a)))
tm_mkpair = lamt $ \h x -> lamt $ \g y -> (FooTerm (FooTerm (ConstTerm (CXAProj1 . CXACurry))
                                                                (appArrow CXAProj2 y)) (appArrow g x))
-}


{-

interpGen :: (forall c. CxtArr c cxt) -> Term cxt a -> CartRepr (Ty a)
interpGen h (LamTerm f) = interpGen h . f h . liftTm . abst


appTm :: Term cxt (TExp a b) -> Term cxt a -> Term cxt b
appTm (LamTerm f) = (f CXAId)
appTm (ConstTerm (CXAAtom f)) = abst . f . interp

appTmNil :: Term CNil (TExp a b) -> Term CNil a -> Term CNil b
appTmNil f = ConstTerm . CXAAtom . interp f . interp

-}

{-
tmBadCase :: Term cxt (TExp (TBase AInt) (TBase AInt))
tmBadCase = LamTerm $ \ x -> case x of (ConstTerm _) -> tmInt 24; _ -> x
-}
{-

type family ToCxt a :: Cxt b where
    ToCxt TUnit = CNil
    ToCxt (TPair a b) = CCons a (ToCxt b)
    ToCxt f = CCons f CNil

type family ToCart a :: TCart b where
    ToCart CNil = TUnit
    ToCart (CCons a cxt) = TPair a (ToCart cxt)

-- as per section 10 of Dosen and Petric, http://arxiv.org/pdf/math/9911073.pdf

data CartArrow :: TCart k -> TCart k -> * where
    CAProj1 :: CartArrow (TPair a b) a
    CAProj2 :: CartArrow (TPair a b) b
    CAConst :: CartArrow a TUnit
    CACompose :: CartArrow b c -> CartArrow a b -> CartArrow a c
    CAPair :: CartArrow c a -> CartArrow c b -> CartArrow c (TPair a b)
    CAId :: CartArrow a a

    CAAtom :: (Show (Repr (Ty b))) => Repr (Ty b) -> CartArrow TUnit (TBase b)

--    CAUncurry :: CartArrow (TPair c a) b -> CartArrow c (TExp a b)
--    CAEval  :: CartArrow (TPair (TExp a b) a) b


deriving instance Show (CartArrow a b)

caCompose :: CartArrow b c -> CartArrow a b -> CartArrow a c
caCompose CAId f = f
caCompose f CAId = f
caCompose (CACompose h g) f = caCompose h (caCompose g f)
--caCompose CAEval (CAPair (CACompose (CAUncurry f) CAProj1) CAProj2) = f
caCompose g f = CACompose g f

--caUncurry :: CartArrow (TPair c a) b -> CartArrow c (TExp a b)
--caUncurry (CACompose CAEval (CAPair (CACompose g CAProj1) CAProj2)) = g
--caUncurry f = CAUncurry f

-- TODO caPair which requires Eq

instance Category CartArrow where
    id = CAId
    (.) = caCompose


data Op c a b = Op (c b a)

instance Category c => Category (Op c) where
    id = C.id
    (Op g) . (Op f) = Op (f . g)

type CArr = Op CxtArr

-}
