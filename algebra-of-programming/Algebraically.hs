{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Algebraically where
import Control.Arrow
import Data.List (inits, tails)

-- Part 1: Fixpoints of Functors, and Algebras on Functors

-- equational reasoning requires equations
-- level up equational reasoning by studying equations more powerful than simple substitutions.
-- data types and functions on them come equipped with laws beyond the obvious.

-- strictly positive recursive types can be written as the fixpoints of "signature functors" like so.

data NatF r = ZeroF | SuccF r

data ListF a r = NilF | ConsF a r

data TreeF a r = LeafF a | BranchF r r

-- Isomorphism between algebras as sets of things to do in each case, and functions out of a functor that encompasses all cases.

type LAlg a b = (a -> b -> b, b)

listFold :: LAlg a b -> ListF a b -> b
listFold (c, z) NilF = z
listFold (c, z) (ConsF a r) = c a r

mkListAlg :: (ListF a b -> b) -> LAlg a b
mkListAlg f = (\x xs -> f (ConsF x xs) , f NilF)

{-
Exercise: Show this is an isomorphism

Exercise: Write the same thing for Trees
-}


listMap :: (a -> b) -> ListF c a -> ListF c b
listMap f NilF = NilF
listMap f (ConsF x y) = ConsF x (f y)

fold :: (a -> b -> b, b) -> [a] -> b
fold (c, z) = foldr c z

a = ((:),[])

{-
exercise: write as pair algebras

1: Sum
2: Length

Now, write them as functor algebras (ListF Int Int -> Int)

substitute and convince yourself these are the same.
-}

-- Part 2: Universal Properties of Folds and equational reasoning

{-
universal property of folds

if h = fold f
<==>
h . listFold a = listFold f . listMap h
-}

lfa :: ListF a [a] -> [a]
lfa = listFold a

up1 :: ([a] -> b) -> LAlg a b -> ListF a [a] -> b
up1 h f = h . listFold a

up2 :: ([a] -> b) -> LAlg a b -> ListF a [a] -> b
up2 h f = listFold f . listMap h

-- Substitute h for fold f, and the following are clearly an identity

up3 :: LAlg a b -> ListF a [a] -> b
up3 f = fold f . listFold a

up4 :: LAlg a b -> ListF a [a] -> b
up4 f = listFold f . listMap (fold f)

-- the universal property shows that this goes the other direction

{-

exercise:

show that up3 and up4 are necessarily the same

-}

{-

exercise:
fold a = id

-}

{-
fold fusion:

h . listFold f = listFold g . listMap h
==>
h . fold f = fold g

-}

ff1 h f g = h . listFold f

ff2 h f g = listFold g . listMap h

{-
*Algebraically> :t ff1
ff1 :: (b -> c) -> LAlg a b -> t -> ListF a b -> c

*Algebraically> :t ff2

ff2 :: (a1 -> c) -> t -> LAlg a c -> ListF a a1 -> c

*Algebraically> :t ff1 `asTypeOf` ff2

ff1 `asTypeOf` ff2 :: (b -> c) -> LAlg a b -> LAlg a c -> ListF a b -> c

h :: b -> c
f :: LALg a b
g :: LAlg a c


h . fold f :: [a] -> c
fold g :: [a] -> c
-}

{-
Exercise: Take h to be show, f to be sum.

Determine g.

-}

sumAlg = ((+),0)
ffex1 :: ListF Integer Integer -> String
ffex1 = show . listFold sumAlg

ffex2 :: ListF Integer Integer -> String
ffex2 = g . listMap (show :: Integer -> String)
    where g :: ListF Integer String -> String
          g = undefined -- ?

{-

exercise: show that

listFold a . fold (mkListAlg (listMap (listFold a))) == id

fold (mkListAlg (listMap (listFold a))) . listFold a == id

-}


-- Part 3: The Banana Split Threorem

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
bsResult1, bsResult2 :: LAlg a b -> LAlg a c -> [a] -> (b,c)
bsResult1 c1 c2 = fold c1 &&& fold c2
bsResult2 c1 c2 = fold (mkListAlg (listFold c1 . listMap fst &&& listFold c2 . listMap snd))


{-
exercise, use the banana split theorem to write a single pass average.
-}

{-
exercise: write the bs theorem as an operation on LAlg explicitly, and argue why it is the same.
-}

-- Part 4: Maximum Segment Sum
-- inspired heavily by http://www.iis.sinica.edu.tw/~scm/2010/maximum-segment-sum-origin-and-derivation/

-- A) list homomorphisms

concatList :: [[a]] -> [a]
concatList = foldr (++) []
-- concatList is a natural transformation -- i.e.
-- map f . concatList = concatList . map (map f)

{-
h :: [a] -> a

h [h xs, h ys] == h (xs ++ ys)
==>
h . concat = h . map h

In such a circumstance, we say h is a "list homomorphism" and it is a special fold that is associative and with a zero element. -- i.e. it is given by the action of a monoid.
-}

{-
Exercise: Give examples of list homomorphisms, and write algebras for them.

Hint: Look at Data.Monoid
-}

-- B) Scanr, inits fusion fusion

tailsAlg :: LAlg a [[a]]
tailsAlg = (go,[[]])
    where go x [] = [[x]]
          go x (y:ys) = (x : y) : y : ys

{-
fold tailsAlg [1,2,3,4]

[[1,2,3,4],[2,3,4],[3,4],[4],[]]
-}

-- note this is reversed from a typical scanr.
scanRight :: LAlg a b -> LAlg a [b]
scanRight (c,z) = (go,[z])
    where go x [] = [c x z]
          go x (y:ys) = c x y : y : ys

{-
By inspection, tails is initial with regards to scans.

scanRight alg = map (fold alg) . fold tailsAlg

rememember fusion
h . listFold f = listFold g . listMap h

take:
h = map (fold alg)
f = tailsAlg
g = scanRight alg

and we see

map (fold alg) . listFold tailsAlg :: ListF a [[a]] -> [a]
listFold (scanRight alg) . listMap (map (fold sumAlg)) :: ListF a [[a]] -> [a]

the two are equal, and therefore by fusion, scanRight alg = map (fold alg) . tailsAlg

Or:

scanr f e = map (foldr f e) . tails

-}

initsAlg :: LAlg a [[a]]
initsAlg = (go,[])
    where go x xs = [x] : map (x:) xs
{-
*Algebraically> fold initsAlg [1,2,3,4,5]
[[1],[1,2],[1,2,3],[1,2,3,4],[1,2,3,4,5]]
-}

--TODO inits fusion
-- map (fold alg) . fold initsAlg == ?

-- C) The problem

testData :: [Integer]
testData = [1,2,3,5,-100,5,1000,-1000,-4,25]

segments :: [Integer] -> [[Integer]]
segments = concat . map inits . tails

mss0 :: [Integer] -> Integer
mss0 = maximum . map sum . segments



mss1, mss2, mss3, mss4 :: [Integer] -> Integer
--inline segments
mss1 = maximum . map sum . concatList        . map inits . tails
-- by naturality of concat
mss2 = maximum . concatList  . map (map sum) . map inits . tails
-- by maximum being a list homomorphism
mss3 = maximum . map maximum . map (map sum) . map inits . tails
-- by map functorality / fusion
mss4 = maximum . map (maximum . map sum . inits) . tails

-- We now denote maximum . map sum . tails as maximum prefix sum
-- maximum segment sum is the maximum of the prefix sums of the tails
-- we wish to manipulate mps into a fold, so that we can use scanr fusion.

mps0,mps1 :: [Integer] -> Integer
mps0 = maximum . map sum . inits
--inits fusion
mps1 = maximum . foldr zplus [0]

zplus x xs = 0 : map (x+) xs
