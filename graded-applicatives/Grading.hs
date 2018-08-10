{-# LANGUAGE KindSignatures, TypeFamilies, ConstraintKinds, PolyKinds, MultiParamTypeClasses, TypeOperators, DataKinds, GADTs, ExistentialQuantification, FlexibleInstances #-}

module Grading where
import GHC.Exts ( Constraint )
import Data.Maybe (mapMaybe)
-- import GHC.TypeLits

-- cf http://conferences.inf.ed.ac.uk/clapscotland/uustalu.pdf
-- https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf

-- Effect is a cut down version of graded monads as per https://hackage.haskell.org/package/effect-monad

{-| Specifies "parametric effect monads" which are essentially monads but
     annotated by a type-level monoid formed by 'Plus' and 'Unit' -}
class Effect (m :: k -> * -> *) where

   {-| Effect of a trivially effectful computation |-}
   type Unit m :: k
   {-| Cominbing effects of two subcomputations |-}
   type Plus m (f :: k) (g :: k) :: k

   {-| Effect-parameterised version of 'return'. Annotated with the 'Unit m' effect,
    denoting pure compuation -}
   ereturn :: a -> m (Unit m) a

   {-| Effect-parameterise version of '>>=' (bind). Combines
    two effect annotations 'f' and 'g' on its parameter computations into 'Plus' -}

   ebind :: m f a -> (a -> m g b) -> m (Plus m f g) b

   ethen :: m f a -> m g b -> m (Plus m f g) b
   x `ethen` y = x `ebind` (\_ -> y)

-- functorality arises from the plus/unit law. Not clear how to express this in general?
efmap :: Effect m => (a -> b) -> m e a -> m (Plus m e (Unit m)) b
efmap f x = x `ebind` (ereturn . f)



-- counter


{-| Define type constructors for natural numbers -}
data N = Z | S N | Inf


type family (:+) n m :: N where
  n :+ Z = n
  n :+ (S m) = S (n :+ m)
  Inf :+ m = Inf
  n :+ Inf = Inf

type family Min n m :: N where
  Min n Inf = n
  Min Inf m = m
  Min n Z = Z
  Min Z m = Z
  Min (S n) (S m) = S (Min n m)

data Vec (n :: N) a = Vec {unVec :: [a]} deriving Show

atMay (x:xs) 0 = Just x
atMay (x:xs) n = atMay  xs (n-1)
atMay [] _ = Nothing

instance Effect Vec where
    {-| Trivial effect annotation is 0 -}
    type Unit Vec = Inf
    {-| Compose effects by addition -}
    type Plus Vec n m = Min n m

    ereturn a = Vec (repeat a)
    (Vec a) `ebind` k = Vec . mapMaybe (uncurry atMay) . (`zip` [0..]) $ map (unVec . k) a

instance Functor (Vec n) where
  fmap = efmap

oneVec :: a -> Vec (S Z) a
oneVec x = Vec [x]

twoVec :: a -> a -> Vec (S (S Z)) a
twoVec x y = Vec [x,y]

threeVec :: a -> a -> a -> Vec (S (S (S Z))) a
threeVec x y z = Vec [x,y,z]


-- regular applicatives from graded monads!

data WrapEff m a = forall n. WrapEff (m n a)

instance Show a => Show (WrapEff Vec a) where show (WrapEff x) = show x

instance (Effect m) => Functor (WrapEff m) where
  fmap f (WrapEff x) = WrapEff (efmap f x)

-- conjecture: every WrapEff of an effect does not necc obey the monad laws, but will obey the applicative laws

instance (Effect m) => Applicative (WrapEff m) where
  pure = WrapEff . ereturn
  WrapEff x <*> WrapEff y = WrapEff $ x `ebind` \x1 -> y `ebind` \y1 -> ereturn (x1 y1)

-- for Vec this recovers ZipList

-- we should be able to give a "times" monoid as well and recover the max-times algebra!

-- todo writer as a graded monad.

-- thm relating distribution over monads and distribution over resultant applicatives -- when does the latter induce the former?

-- also when does a WrapEff a actually yield a monad?