{-# LANGUAGE DeriveFunctor, StandaloneDeriving, UndecidableInstances, PolyKinds, MultiParamTypeClasses, FlexibleInstances #-}

module IT where
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Data.Functor.Compose
import Debug.Trace
import Control.Applicative


{-
traversal needs to be with a free monoid in the topos of trees
http://comonad.com/reader/2015/free-monoids-in-haskell/

in the topos of trees should still be a corresp between poly endofunctor and containers

what subset of containers gets picked out by guarded recursive datatypes

Later f a -> f Later a

"predict"

Predictable applicatives -- credit james

Unpredictable traversals can't be infinite

Last applicative over a biinfinite list

-}

-- Nakhano's later modality for guarded recursion, as an applicative functor a la "Productive Coprogramming with Guarded Recursion": https://bentnib.org/productive.pdf
newtype Later a = Later a deriving (Functor, Show)

instance Applicative Later where
  pure = Later
  Later f <*> Later x = Later (f x)

lfix :: (Later a -> a) -> a
lfix f = let x = f (pure x) in x

data Stream a = Nil | Cons a (Later (Stream a)) deriving (Functor, Show)

-- not really a monoid at all, its a tensor over later?? also we have Stream (Later a) -> Later (Stream a)
-- so its f a -> f (Later a) -> f a
-- can write append in terms of that
-- can write as stream = a : Later a : Later Later a, etc

-- actually, given a stream of length n, we can cons on a stream with n laters, so its bi-indexed objects (length and later depth) and the result is the length of the two summed. --

-- it becomes a graded monoid if we lift the left until it fits, but then you get this weird indexing summation.
-- so its abolutely Not Free.

instance Semigroup a => Semigroup (Stream a) where
  (<>) = lfix $ \f x y ->
            case (x, y) of
              (Nil, _) -> y
              (_, Nil) -> x
              (Cons a s, Cons b s') -> Cons (a <> b) (f <*> s <*> s')

instance Monoid a => Monoid (Stream a) where
  mempty = Cons mempty (Later Nil)

shiftStream :: Monoid a => Later (Stream a) -> Stream a
shiftStream = Cons mempty


-- can we use lattice theory to get infinite monoid generalizations?

-- can we sequence a stream of streams?

-- credit for name predict to James Deikun

class Predict f where
  predict :: Later (f a) -> f (Later a)
  -- can't give check :: f (Later a) -> Later (f a) because of reader.
  -- this really blows up in the case of the update monad.
  -- we can factorize out the delay in the state, but that's sort of uninteresting
  delay :: f a -> f a

-- we need an evaluate morphism :: f a -> Eventually (f a) and the property that delay . evaluate = id. delay should be uniquely defined by the predict . pure equation.

-- the law should be an interaction with applicative
-- fmap Later . liftA2 (,) x == liftA2 (,) x . predict . Later !!!!

-- or rather
-- \x y -> (fmap (fmap Later) . liftA2 (,) x) y == (liftA2 (,) x . predict . Later) y

testProp x y = (fmap (fmap Later) . liftA2 (,) x) y == (liftA2 (,) x . predict . Later) y

testProp1 x y = (fmap (fmap Later) . liftA2 (,) x) y

testProp2 x y = (liftA2 (,) x . predict . Later) y

w1 = tell (Cons 1 (Later Nil)) :: Writer (Stream (Sum Int)) ()
w2 = tell (Cons 3 (Later Nil)) :: Writer (Stream (Sum Int)) ()

-- sidenote: we can anti-commute a reader over finite but not in general
foo :: (Bool -> Later a) -> Later (Bool -> a)
foo f = (\t f x -> if x then t else f) <$> (f True) <*> (f False)

-- predict . pure = fmap Later . delay
-- sequence . fmap pure = delay^n . pure ?

-- check :: f a -> Eventually f a
-- check . delay =~ id
-- recover . predict =~ id

-- law for diff. not exactly if you erase laters you get the same thing.
-- take law for traversals, put in this setting, induce a law for Predict
-- distributive law, sort of?

-- we can state the traversable law with delay, but we need recover or the like to state the full diff law!

-- any structure that's traversable is infinitely traversable, prove this

instance Predict Later where
  predict = id
  delay = id

instance Predict Identity where
  predict = Identity . fmap runIdentity
  delay = id

instance Predict (Reader r) where
  predict x = reader $ \r -> fmap (($ r) . runReader) x
  delay = id

instance Monoid w => Predict (Writer (Stream w)) where
  predict x = writer $ (fst . runWriter <$> x, shiftStream $ snd . runWriter <$> x)
  delay x = case runWriter x of
     (x, y) -> writer (x, shiftStream $ pure y)

class Sequence t where
  ssequence :: (Applicative f, Predict f) => t (f a) -> f (t a)

instance Sequence Stream where
  ssequence = lfix $ \rec x -> case x of
     Nil -> pure Nil
     Cons a s -> Cons <$> a <*> predict (rec <*> s)

data Tree a = TNil | TBranch a (Later (Tree a)) (Later (Tree a)) deriving (Functor, Show)

instance Sequence Tree where
  ssequence = lfix $ \rec x -> case x of
     TNil -> pure TNil
     TBranch a x y -> TBranch <$> a <*> predict (rec <*> x) <*> predict (rec <*> y)

instance (Functor f, Predict f, Predict g) => Predict (Compose f g) where
  predict = Compose . fmap predict . predict . fmap getCompose
  delay (Compose x) = Compose (fmap delay . delay $ x)

data Update s a = Update {runUpdate :: (Stream s -> (Stream s,a))} deriving Functor -- stream of s to single s

instance Monoid s => Applicative (Update s) where
  pure x = Update $ \s ->  (s, x)
  f <*> x = ap f x

instance Monoid s => Monad (Update s) where
  Update x >>= f = Update $ \s -> let (u, x') = x s in runUpdate (f x') (u <> s)

instance Monoid s => Predict (Update s) where
  predict x = Update $ \s -> let rxs = fmap (($ s) . runUpdate) x in
   (shiftStream (fmap fst rxs), fmap snd rxs)
  delay x = Update $ \s -> let (a, b) = runUpdate x s in (shiftStream . pure $ a, b)



listToStream (x:xs) = Cons x . Later $ listToStream xs
listToStream [] = Nil

finiteStream :: Stream Int
finiteStream = Cons 1 . Later . Cons 2 . Later . Cons 4 . Later $ Nil

headS (Cons a _) = a
headS Nil = mempty

tailS (Cons _ x) = x
tailS Nil = Later Nil

updateStream :: Stream (Update (Sum Int) Int)
updateStream = listToStream [getU $ getSum . headS, putU 1 2, getU $ getSum . headS, putU 4 6, getU $ getSum . headS]

putU :: a -> b -> Update a b
putU x b = Update $ \s -> (Cons x $ Later Nil, b)

getU :: (Stream s -> a) -> Update s a
getU f = Update $ \s -> (Nil, f s)

goU (Update f) = f Nil


instance Monoid s => Predict (State (Stream s)) where
  predict x = state $ \s -> let rs = fmap (`runState` s) x
                            in (fmap fst rs, shiftStream (fmap snd rs))
  delay x = state $ \s -> let rs = runState x s
                            in (fst rs, shiftStream . pure . snd $ rs)

one :: a -> Stream a
one x = Cons x $ Later Nil

stateStream :: Stream (State (Stream (Sum Int)) Int)
stateStream = listToStream [getSum . headS <$> get, put (one 1) >> pure 2, getSum . headS <$> get, put (one 4) >> pure 6, getSum . headS <$> get]

straverse g = ssequence . fmap g

-- update is better than state.

-- Eventually vs. Stream. "partial accumulation over time"

-- interesting example -- iterate over a stream of data, producing a stream of of observation and also output data

-- this is precisely stream transducers

-- nb, can predict necessarily infinite streams, but not possibly terminating ones -- gotta write a distinct stram type

instance Applicative Stream where
  pure a = Cons a . Later $ pure a
  (<*>) = lfix $ \rec s1 s2 -> case (s1, s2) of
              (Cons x xs, Cons y ys) -> Cons (x y) (rec <*> xs <*> ys)
              (Nil,_) -> Nil
              (_,Nil) -> Nil

{-
-- can't work because we only do infinite streams, and the "crossy" stream applicative is necessarily not infinite given the pure instance
instance Applicative Stream where
  pure a = Cons a . Later $ Nil
  (<*>) = lfix $ \rec s1 s2 -> case (s1, s2) of
              (Nil,_) -> Nil
              (_,Nil) -> Nil
              (Cons x xs, _) -> fmap x s2 `sappend` (rec <*> xs <*> Later s2)
            where sappend :: Stream a -> Later (Stream a) -> Stream a
                  sappend xs (Later ys) = trace "sappend" $ listToStream (streamToList xs <> streamToList ys)
-}

instance Predict Stream where
  predict x = Cons (fmap headPartial x) (fmap (predict . tailPartial) x) -- not using lfix?
     where headPartial (Cons e _) = e
           headPartial _ = error "headPartial" -- works for infinite streams but not normal streams.
           tailPartial (Cons x xs) = xs
           tailPartial Nil = error "nil"
  delay = id

tfS = listToStream [True, False]

streamToList Nil = []
streamToList (Cons a (Later b)) = a : streamToList b

-- on infinite streams, can transpose an infinite stream of infinite streams using the zip applicative.

-- can we even speak of the list applicative?

-- ssequence . listToStream $ repeat tfS

{-

we've shown diff -> ssequence
can we show ssequence -> diff?

lseq :: Later (f a) -> f (Later a) -- i.e. diff is precisely sequence for Later (show it obeys laws??)

-- given any x :: a, we have fmap (shead . stail) (cons (pure x) (fmap ssingleton z))


-}

{-
Laws for ssequence:
 ssequence . fmap Identity = Identity
 ssequence . fmap Compose = Compose . fmap ssequence . sseqence
 t . ssequence = ssequence . fmap t for every applicative transformation t or perhaps differential applicative transformation

*IT> straverse pure finiteStream :: Writer (Stream Any) (Stream Int)
WriterT (Identity (Cons 1 (Later (Cons 2 (Later (Cons 4 (Later Nil))))),Cons (Any {getAny = False}) (Later (Cons (Any {getAny = False}) (Later (Cons (Any {getAny = False}) (Later Nil)))))))

-- we get a stream of results, but pure gives a single result!


instance Sequence Stream where
  ssequence = lfix $ \rec x -> case x of
     Nil -> pure Nil
     Cons a s -> Cons <$> a <*> predict (rec <*> s)

instance (Functor f, Diff f, Diff g) => Diff (Compose f g) where
  predict = Compose . fmap predict . predict . fmap getCompose

-- sequence of a composed stream
  ssequence = case x of
     Nil -> pure Nil
     Cons a s -> Cons <$> a <*> (Compose . fmap predict . predict . fmap getCompose) (ssequence s)

-- sequence of a plain stream
  ssequence = case x of
     Nil -> pure Nil
     Cons a s -> Cons <$> a <*> predict (ssequence s)

-- fmap of sequence of a plain stream -- we substitute in the case on the created stream
  ssequence = case Cons a (predict (ssequence s)) of
     Cons a s1 -> Cons <$> a <*> predict (ssequence s1)

-- substitute
  ssequence = case Cons a (predict (ssequence s)) of
     Cons a s1 -> Cons <$> a <*> predict (ssequence ((predict (ssequence s))))

-- ssequence doubled should somehow turn into needing to fmap the predict into it.

-- equationally this should work, somehow

-- naturality is tricky!

-- can we prove a "representation theorem" for infinite traversals?
https://www.cs.ox.ac.uk/jeremy.gibbons/publications/uitbaf.pdf

-- predict . unpredict
-}
{-

junk

class LApplicative f i where
  lpure :: a -> f i a
  lap   :: f i (a -> b) -> f (Compose Later i) a -> f i b

class LDiff f where
  lpredict :: Later (f i a) -> f (Compose Later i) (Later a)
  lunpredict :: f i a -> f (Compose Later i) a

class Sequence t where
  ssequence :: (Functor (f i), LApplicative f i, LDiff f) => t (f i a) -> f i (t a)

-- sequence instances
instance Sequence Stream where
  ssequence = lfix $ \rec x -> case x of
     Nil -> lpure Nil
     Cons a s -> (Cons <$> a) `lap` (lpredict $ rec <*> s)

data Tree a = TNil | TBranch a (Later (Tree a)) (Later (Tree a)) deriving (Functor, Show)

instance Sequence Tree where
  ssequence = lfix $ \rec x -> case x of
     TNil -> lpure TNil
     TBranch a x y -> (TBranch <$> a) `lap` (lpredict $ rec <*> x) `lap` (lpredict $ rec <*> y)


-- lapplicative instances
data IReader r i a = IReader {runIReader :: (r -> a)}

instance LApplicative (IReader r) i where
  lpure = IReader . const
  lap (IReader f) (IReader x) = IReader $ \r -> (f r) (x r)

instance LDiff (IReader r) where
  lpredict x = IReader $ \r -> fmap (($ r) . runIReader) x
  lunpredict (IReader x) = IReader x

-- can pushindexing in to writer, get rid of it.

data IWriter w i a = IWriter {runIWriter :: (i (Stream w), a)}


instance (Monoid w, Applicative i, Diff i) => LApplicative (IWriter w) i where
  lpure x = IWriter (pure mempty, x)
  lap (IWriter (s, f)) (IWriter (s', x)) = IWriter (mappend <$> s <*> (fmap shiftStream . predict . getCompose $ s'), f x)

-}
-- what algebraic structure corresponds to trees?