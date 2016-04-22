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

data CxtArr :: Cxt a -> Cxt a -> *  where
  CXAId  :: CxtArr a a
  CXACompose :: CxtArr b c -> CxtArr a b -> CxtArr a c
  CXANil :: CxtArr a CNil

  CXAAtom :: CartRepr (Ty a) -> CxtArr cxt (CCons a cxt)

  CXAWeaken :: CxtArr (CCons a cxt) cxt

  CXAEval  :: CxtArr (CCons (TPair (TExp a b) a) cxt) (CCons b cxt)

  CXAAbs   :: CxtArr (CCons a cxt) (CCons b CNil) ->  CxtArr cxt (CCons (TExp a b) CNil)
  CXALam    :: (forall c. CxtArr c cxt -> CxtArr c (CCons a c2) -> CxtArr c (CCons b c2)) -> CxtArr cxt (CCons (TExp a b) c2)

  -- we don't really need these?
  CXAPair  :: CxtArr cxt (CCons a c2) -> CxtArr cxt (CCons b c2) -> CxtArr cxt (CCons (TPair a b) c2)
  CXAPairProj1 :: CxtArr (CCons (TPair a b) cxt) (CCons a cxt)
  CXAPairProj2 :: CxtArr (CCons (TPair a b) cxt) (CCons b cxt)


-- As per section 10 of  http://arxiv.org/pdf/math/9911073.pdf

cxaCompose :: CxtArr b c -> CxtArr a b -> CxtArr a c
cxaCompose CXAId f = f
cxaCompose f CXAId = f
cxaCompose h (CXACompose g f) = CXACompose (cxaCompose h g) f
cxaCompose CXAEval (CXAPair (CXACompose (CXAAbs f) CXAWeaken) CXAId) = f
cxaCompose CXAEval (CXAPair (CXACompose (CXALam f) CXAWeaken) CXAId) = f CXAWeaken CXAId
cxaCompose CXAPairProj1 (CXAPair a b) = a
cxaCompose CXAPairProj2 (CXAPair a b) = b

--TODO fix all the rules in composition... maybe move abs to deal with pairs somehow?
cxaCompose g f = CXACompose g f

-- TODO write cxaPair as a "smart constructor"

-- todo make instance of classes in categories lib?
instance Category CxtArr where
    id = CXAId
    (.) = cxaCompose

-- terms here are elements or fibers of presheaves.
newtype Term cxt a = Term (CxtArr cxt (CCons a CNil))

unTerm :: Term cxt a -> CxtArr cxt (CCons a CNil)
unTerm (Term x) = x

lamTerm :: (forall c. CxtArr c cxt -> Term c a -> Term c b) -> Term cxt (TExp a b)
lamTerm f = Term (CXALam (\m x -> unTerm (f m (Term x))))

appTerm :: Term cxt (TExp a b) -> Term cxt a -> Term cxt b
appTerm f x = Term (CXAEval . (CXAPair (unTerm f) (unTerm x)))

appArrow :: CxtArr c d -> Term d a -> Term c a
appArrow h (Term g) = Term $ g . h

interp :: Term CNil a -> CartRepr (Ty a)
interp (Term (CXAAtom x)) = x
interp (Term (CXACompose f g)) =  interp (appArrow g (Term f))
interp (Term (CXALam f)) = interp . Term . f CXAId . CXAAtom
interp (Term (CXAAbs f)) = interp (Term (CXALam $ \_ x -> f . x))
interp (Term (CXAPair f g)) = (interp (Term f), interp (Term g))

weakenTerm :: Term cxt a -> Term (CCons b cxt) a
weakenTerm = appArrow CXAWeaken

liftTm :: Term CNil a -> Term cxt a
liftTm = appArrow CXANil

varTm :: Term (CCons a CNil) a
varTm = Term CXAId

--TODO can we write subst?
-- subst :: Term (CCons a cxt) t -> Term cxt a -> Term cxt t
-- subst = foo...

test = (interp (tm_id :: Term cxt (TExp (TBase AInt) (TBase AInt)))) $ 12

abst :: CartRepr (Ty a) -> Term CNil a
abst = Term . CXAAtom


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



{-
unTerm :: Term cxt a -> CxtArr cxt (CCons a CNil)
unTerm (ConstTerm x) = x
unTerm (AppTerm f x) = CXAEval . (CXAPair (unTerm f) (unTerm x))
unTerm (LamTerm f) = unTerm $ abstTerm (f CXAProj2 (appArrow CXAProj1 $ ConstTerm CXAId))

abstTerm :: Term (CCons a cxt) b -> Term cxt (TExp a b)
abstTerm = undefined
-}

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

-- foo = lamt $ \h x -> appArrow CXAEval x

{-
tm_badcata

tm_s = lam $ \f -> lam $ \g -> lam $ \x -> AppTerm (AppTerm f x) (AppTerm g x)

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
