{-# LANGUAGE DataKinds, TypeOperators, MultiParamTypeClasses, TypeFamilies, GADTs, ScopedTypeVariables, RankNTypes, PolyKinds, StandaloneDeriving, FlexibleContexts #-}

module Lambek(
) where
import Control.Category as C

{-
Explorations in lambda terms as elements of presheaves, or generally as slices in a category of contexts.
-}

data ABase = AInt | AString

type family Repr a
data Ty a
type instance Repr (Ty AInt) = Int
type instance Repr (Ty AString) = String

data TCart b = TUnit | TPair (TCart b) (TCart b) | TExp (TCart b) (TCart b) | TBase b

data Cxt b = CCons (TCart b) (Cxt b) | CNil

-- CxtArr a b is a judgment
--   a
-- -----
--   b

data CxtArr :: Cxt a -> Cxt a -> * where
  CXAId  :: CxtArr a a
  CXANil :: CxtArr a CNil
  CXACompose :: CxtArr b c -> CxtArr a b -> CxtArr a c

  CXAAtom :: Repr (Ty b) -> CxtArr cxt (CCons (TBase b) cxt)

  CXAProj1 :: CxtArr (CCons a cxt) (CCons a CNil)
  CXAProj2 :: CxtArr (CCons a cxt) cxt

  CXACurry :: CxtArr (CCons a (CCons b cxt)) (CCons (TPair a b) cxt)
  CXAUncurry :: CxtArr (CCons (TPair a b) cxt) (CCons a (CCons b cxt))

-- todo make simplicial? or make product of categories? how to lift morphisms in the base category?

cxaCompose :: CxtArr b c -> CxtArr a b -> CxtArr a c
cxaCompose CXAId f = f
cxaCompose f CXAId = f
cxaCompose (CXACompose h g) f = cxaCompose h (cxaCompose g f)
cxaCompose g f = CXACompose g f

instance Category CxtArr where
    id = CXAId
    (.) = cxaCompose

-- terms here are elements or fibers of presheaves. We want the whole thing? Ans -- in all contexts?

data Term cxt a where
    ConstTerm :: CxtArr cxt (CCons a CNil) -> Term cxt a --representable
    LamTerm   :: (forall c cxt1. CxtArr (CCons c cxt1) cxt -> Term (CCons c cxt1) a -> Term (CCons c cxt1) b) -> Term cxt (TExp a b)
    -- LTm       :: (forall c. CxtArr c cxt -> Term c a -> Term cxt b) -> Term cxt (TExp a b)
    AppTerm   :: Term cxt (TExp a b) -> Term cxt a -> Term cxt b

    AbsTerm   :: Term (CCons a cxt) b -> Term cxt (TExp a b)
    FooTerm   :: Term (CCons a cxt) b -> Term cxt a -> Term cxt b
--TODO: Cata representation of terms?

appArrow :: CxtArr c d -> Term d a -> Term c a
appArrow h (ConstTerm g) = ConstTerm $ g C.. h
appArrow h (LamTerm f)   = LamTerm $ \g x -> f (h C.. g) x
appArrow h (AppTerm g x) = AppTerm (appArrow h g) (appArrow h x)

-- revArr :: CxtArr c d -> Term c a -> Term d a
-- revArr = undefined

tmInt :: Int -> Term CNil (TBase AInt)
tmInt i = ConstTerm (CXAAtom i)

lam :: (forall c. Term c a -> Term c b) -> Term cxt (TExp a b)
lam f = LamTerm $ \ h -> f

lamt :: (forall c cxt1. CxtArr (CCons c cxt1) cxt -> Term (CCons c cxt1) a -> Term (CCons c cxt1) b) -> Term cxt (TExp a b) --(forall c. CxtArr c cxt -> Term c a -> Term c b) -> Term cxt (TExp a b)
lamt f = LamTerm f

tm_id = lam $ \x -> x

tm_k = lam $ \x -> LamTerm $ \g y -> appArrow g x

tm_s = lamt $ \h f -> lamt $ \h1 g -> lamt $ \h2 x -> AppTerm (AppTerm (appArrow (h1 C.. h2) f) x) (AppTerm (appArrow h2 g) x)

--tm_mkpair :: Term cxt (TExp a (TExp a1 (TPair a1 a)))
tm_mkpair = lamt $ \h x -> lamt $ \g y -> (FooTerm (FooTerm (ConstTerm (CXAProj1 C.. CXACurry))
                                                                (appArrow CXAProj2 y)) (appArrow g x))

--AbsTerm (AbsTerm (ConstTerm (CXAProj1 C.. CXACurry)))
            --lamt $ \h x -> lamt $ \g y -> (appArrow _ (ConstTerm (CXAProj1 C.. CXACurry)))

weakenTerm :: Term cxt a -> Term (CCons b cxt) a
weakenTerm = appArrow CXAProj2

{-
ltm f = LTm $ \h x -> f (revArr h x)

tm_id1 = LTm $ \h x -> revArr h x

tm_k1 = LTm $ \h x -> LTm $ \g y -> revArr h x

tm_s1 = LTm $ \h f -> LTm $ \h1 g -> LTm $ \h2 x -> AppTerm (AppTerm (revArr h f) (revArr h2 x)) (AppTerm (revArr h1 g) (revArr h2 x))
-}
{-
tm_badcata

tm_s = lam $ \f -> lam $ \g -> lam $ \x -> AppTerm (AppTerm f x) (AppTerm g x)

-}

{-
tmBadCase :: Term cxt (TExp (TBase AInt) (TBase AInt))
tmBadCase = LamTerm $ \ x -> case x of (ConstTerm _) -> tmInt 24; _ -> x
-}
     --        PLam   :: (forall c. Term (CCons c cxt) a -> Term (CCons c cxt) b) -> Term cxt (TyArr a b)

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
    (Op g) . (Op f) = Op (f C.. g)

type CArr = Op CxtArr

-}
