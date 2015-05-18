{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Algebraically where
import Control.Arrow

-- equational reasoning requires equations
-- level up equational reasoning by studying equations more powerful than simple substitutions.
-- data types and functions on them come equipped with laws beyond the obvious.

data ListF a r = NilF | ConsF a r

-- banana split
-- Isomorphism between algebras as sets of things to do in each cae, and functions out of a functor that encompasses all cases.

type LAlg a b = (a -> b -> b, b)

mkListAlg :: (ListF a b -> b) -> LAlg a b
mkListAlg f = (\x xs -> f (ConsF x xs) , f NilF)

listFold :: LAlg a b -> ListF a b -> b
listFold (c, z) NilF = z
listFold (c, z) (ConsF a r) = c a r

listMap :: (a -> b) -> ListF c a -> ListF c b
listMap f NilF = NilF
listMap f (ConsF x y) = ConsF x (f y)

fold (c, z) = foldr c z

a = ((:),[])

{-
exercise: write as pair algebras

1: Sum
2: Length

Now, write them as functor algebras (ListF Int Int -> Int)

substitute and convince yourself these are the same.
-}

{-
universal property of folds

if h = fold f
<==>
h . listFold a = listFold f . listMap h
-}

lfa :: ListF a [a] -> [a]
lfa = listFold a

up1 :: LAlg a b -> ListF a [a] -> b
up1 f = fold f . listFold a

up2 :: LAlg a b -> ListF a [a] -> b
up2 f = listFold f . listMap (fold f)


{-

exercise:
fold a = id

-}

{-

h . listFold f = listFold g . listMap h
==>
h . fold f = fold g

h . fold f === h . fold (cata q

-}


{-

exercise: show that

listFold a . fold (mkListAlg (listMap (listFold a))) == id

fold (mkListAlg (listMap (listFold a))) . listFold a == id

-}


bs1, bs2, bs3, bs4, bs5, bs6 :: LAlg a b -> LAlg a c -> ListF a [a] -> (b,c)
bs1 c1 c2 = (fold c1 &&& fold c2) . listFold a
-- split fusion
bs2 c1 c2 = fold c1 . listFold a &&& fold c2 . listFold a
-- properties of fold
bs3 c1 c2 = listFold c1 . listMap (fold c1) &&& listFold c2 . listMap (fold c2)
-- split expansion
bs4 c1 c2 = listFold c1 . listMap (fst . (fold c1 &&& fold c2)) &&&
            listFold c2 . listMap (snd . (fold c1 &&& fold c2))
-- functor splitting
bs5 c1 c2 = listFold c1 . listMap fst . listMap (fold c1 &&& fold c2) &&&
            listFold c2 . listMap snd . listMap (fold c1 &&& fold c2)
-- split fusion (backwards)
bs6 c1 c2 = (listFold c1 . listMap fst &&& listFold c2 . listMap snd) . listMap (fold c1 &&& fold c2)

{-
by the universal property of lists, bs1 == bs6 implies that
(fold c1 &&& fold c2) === fold (listFold c1 . listMap fst &&& listFold c2 . listMap snd)
-}
bsResult1, bsResult2, bsResult3 :: LAlg a b -> LAlg a c -> [a] -> (b,c)
bsResult1 c1 c2 = fold c1 &&& fold c2
bsResult2 c1 c2 = fold (mkListAlg (listFold c1 . listMap fst &&& listFold c2 . listMap snd))


{-
exercise, use the banana split theorem to write a single pass average.
-}

{-
exercise: write the bs theorem as an operation on lalgs explicitly, and argue why it is the same.
-}

bsResult3 (c1,z1) (c2,z2) = fold (\x (y1,y2) -> (c1 x y1, c2 x y2), (z1,z2))





---

class Buildable f a where
    build :: ((a -> f a -> f a) -> f a -> f a) -> f a
    build g = g insert unit

    singleton :: a -> f a
    singleton x = build (\c n -> c x n)

    unit ::  f a
    unit = build (\cons nil -> nil)

    insert :: a -> f a -> f a
    insert x xs = build (\cons nil -> x `cons` xs)

fromList :: Buildable f a => [a] -> f a
fromList xs = foldr insert unit xs

data PairF f g a = PairF (f a, g a)

instance (Buildable f a, Buildable g a) => Buildable (PairF f g) a where
  unit = PairF (unit, unit)
  insert x (PairF (xs, ys)) = PairF (insert x xs, insert x ys)
--
