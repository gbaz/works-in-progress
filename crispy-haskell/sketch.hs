{-# LANGUAGE StaticPointers #-}
{-# LANGUAGE TupleSections #-}

import  GHC.StaticPtr
import Data.Typeable

type Global = StaticPtr

local :: Global a -> a
local = deRefStaticPtr

x =  static (5 ::  Int) :: Global Int

y :: Global Int
y = let z = 20 in static (local x + 5)

z = 20

class CFunctor f where
  cmap :: Global (a -> b) -> f a -> f b

class (Typeable w, CFunctor w) => CComonad w where
  -- |
  -- @
  -- 'extract' . 'fmap' f = f . 'extract'
  -- @
  extract :: w a -> a

  -- |
  -- @
  -- 'duplicate' = 'extend' 'id'
  -- 'fmap' ('fmap' f) . 'duplicate' = 'duplicate' . 'fmap' f
  -- @
  duplicate :: w a -> w (w a)

  -- |
  -- @
  -- 'extend' f = 'fmap' f . 'duplicate'
  -- @
  extend :: Global (w a -> b) -> w a -> w b


-- toss in a label?
data Crisp a = Crisp a
instance IsStatic Crisp where
  fromStaticPtr = Crisp . local

instance CFunctor Crisp where
  cmap f (Crisp a) = Crisp (local f a)

cjoin :: Crisp (Crisp a) -> Crisp a
cjoin (Crisp x) = x


-- ask ian orton / licata uses?



instance CComonad Crisp where
  extract (Crisp a) = a
  duplicate = Crisp
  extend f x = Crisp (local f x)


strength :: Functor f => a -> f b -> f (a,b)
strength x = fmap (x,)

{-
-- can't do it!
cstrength :: (Typeable a, Typeable b, CFunctor f) => a -> f b -> f (a,b)
cstrength x = cmap (static (x,))
-}

-- foo :: Exists Gamma. (Gamma, Crisp ((Gamma -> Int) -> String))
-- bar :: Global (