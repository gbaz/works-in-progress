{-# LANGUAGE DataKinds, TypeOperators, MultiParamTypeClasses, TypeFamilies, GADTs, ScopedTypeVariables, RankNTypes, StandaloneDeriving, TypeInType, PolyKinds, TypeApplications, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

module Polystream where
import Data.Proxy
import Data.List
import qualified Data.Map as M
import Debug.Trace
-- import GHC.TypeLits

data Nat = Z | S Nat

class ToInt a where
  toInt :: a -> Int

instance ToInt (Proxy Z) where
  toInt _ = 0

instance ToInt (Proxy n) => ToInt (Proxy (S n)) where
  toInt _ = 1 + toInt (Proxy :: Proxy n)


-- todo elim vec case?
data Vec n a where
  VZ :: a -> Vec Z a
  VS :: a -> Vec m a -> Vec (S m) a

vec2List :: Vec n a -> [a]
vec2List (VZ a) = [a]
vec2List (VS a v) = a : vec2List v

-- move to level n, m variables and this works without singleton... hrm.
-- level n, (m+1) variables
data SVec n m a where
  SUnit :: a -> SVec Z m a
  SSingleton :: ToInt (Proxy n) => a -> SVec n Z a
  SBase :: Vec m a -> SVec (S Z) m a
  -- at level n, for a given variable it splits into all level n-1 with that variable added plus all level n-1 with that variable not present and the next variable bumped, and so on until we've eliminated all variables
  SCons :: SDesc n (S m) a -> SVec (S n) (S m) a

 -- SVec n (S m) a -> SVec n m a -> SVec (S n) (S m) a

data SDesc n m a where
 SDNil :: SVec n Z a -> SDesc n Z a
 SDCons :: SVec n (S m) a -> SDesc n m a -> SDesc n (S m) a


numvars v = take (length (vec2List v)) [(1::Int)..]

type Trm = M.Map Int Int

bumpVarName :: M.Map Trm a -> M.Map Trm a
bumpVarName = M.mapKeys (M.mapKeys (+1))

bumpVar :: Int -> M.Map Trm a -> M.Map Trm a
bumpVar n = M.mapKeys (M.insertWith (+) n 1)

sToProxy :: SVec n m a -> Proxy n
sToProxy = undefined

mkMap :: Num a => SVec n m a -> M.Map Trm a
mkMap (SUnit a) = M.singleton M.empty a
mkMap x@(SSingleton a) = trace (show $ (toInt (sToProxy x))) $ M.singleton (M.singleton 1 (toInt (sToProxy x))) a -- TODO different count for each n
mkMap (SBase v) = M.fromList $ zip (map (`M.singleton` 1) $ numvars v) (vec2List v)
mkMap (SCons x) = mkMapDesc x

mkMapDesc :: Num a => SDesc n m a -> M.Map Trm a
mkMapDesc (SDCons x y) = M.unionWith (+) (bumpVar 1 $ mkMap x) (bumpVarName $ mkMapDesc y)
mkMapDesc (SDNil v) = bumpVar 1 $ mkMap v

-- mkMap (SCons x) = M.unionWith (+) (bumpVar 1 $ mkMap x) (bumpVarName $ bumpVar 1 (mkMap y))

foo1 :: SVec ('S 'Z) ('S ('S 'Z)) Integer -- level 1, 3 elements
foo1 = SCons (SDCons (SUnit 1) (SDCons (SUnit 2) (SDNil (SUnit 3))))

foo :: SVec ('S 'Z) ('S 'Z) Integer -- level 1, 2 elements
foo = SBase (VS 2 (VZ 1))
bar :: SVec ('S 'Z) 'Z Integer -- level 1, 1 element
bar = SBase (VZ 5)

baz :: SVec ('S ('S 'Z)) ('S 'Z) Integer -- level 2, 2 elements
baz = SCons (SDCons foo (SDNil bar))

quux :: SVec ('S ('S ('S 'Z))) ('S 'Z) Integer -- level 3, 2 elements
quux = SCons (SDCons baz (SDNil (SSingleton 13)))

bill :: SVec ('S ('S 'Z)) ('S ('S 'Z)) Integer
bill = SCons (SDCons (SBase (VS 5 (VS 7 (VZ 15)))) (SDCons foo (SDNil (SSingleton 45))))


-- asdf = SCons (SDCons baz (SDNil _))










-- v is num of variables, n is number of variables (i.e. level in series)
data Series v n a where
   SZ :: a -> Series Z v a
   SE :: a -> Series v v a
--   SE ::
   SS ::    Series v (S n) a
         -> Series v n a
         -> Series (S v) (S n) a

seriesSize :: Series v n a -> Int
seriesSize (SZ _) = 1
seriesSize (SE _) = 1
seriesSize (SS a b) = seriesSize a + seriesSize b

deriving instance Show a => Show (Series v n a)


data Binom n k a where
  BNull :: Binom n (S n) a
  BUnit :: a -> Binom n n a
  BUnit' :: a -> Binom n Z a
  BS :: Binom n (S k) a  -> Binom n k a -> Binom (S n) (S k) a


deriving instance Show a => Show (Binom n k a)

b0 :: Binom Z Z Double
b0 = BUnit 1

b1_1 :: Binom (S Z) Z Double
b1_1 = BUnit' 1

b1_2 :: Binom (S Z) (S Z) Double
b1_2 = BUnit 1

b2_1 :: Binom (S (S Z)) Z Double
b2_1 = BUnit' 1

b2_2 :: Binom (S (S Z)) (S Z) Double
b2_2 = BS b1_2 b1_1

b2_3 :: Binom (S (S Z)) (S (S Z)) Double
b2_3 = BUnit 1

-- b1_1 :: Binom (S Z) Z Double
-- b1_1 = BS BNull _
--b1_1 = BS BNull (BZ 1)
--b1_1 = BSZ 1

fac n | n > 0 = n * fac (n - 1)
      | otherwise = 1

choose n k = fac n / (fac k * fac (n - k))
chooseReplace n k = choose (n + k - 1) k
