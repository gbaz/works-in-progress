{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}

module PlanarC where
import Debug.Trace


-- context is generated by zero, extension (add one to the right), usage (move turnstile left), and closure (chop off right side of turnstile).

data Nat = Z | S Nat deriving (Read, Show, Eq)

cnat :: Nat -> Int
cnat Z = 0
cnat (S x) = 1 + cnat x

-- data Tree = L | B Tree Tree deriving (Read, Show, Eq)

data C = C Nat [Nat] deriving (Read, Show, Eq)

empty = C Z [Z]

intro :: C -> [C]
intro (C h ts) = [C (S h) (Z : ts)]

shift :: C -> [C]
shift (C (S h) (t:ts)) = [C h (S t : ts)]
shift _ = []

-- no apply?
app :: C -> [C]
app (C h (S (S t) : ts)) = [C h (S t : ts)]
app _ = []

-- can't close unless discharged.

close :: C -> [C]
close (C h (S Z:t:ts)) | cnat h < length (t:ts) = [C h (S t : ts)]
                       | otherwise = []
-- close (C h (S Z:[])) =  [C h []]
-- close (C h (Z:ts)) =  Just (C h ts)
close _ = []

data Op = CI | CA | CS | CC deriving (Read, Show, Eq, Ord)

genTerm :: Int -> [(C,[Op])]
genTerm x = go x (empty,[])
  where go n (c,os) = is ++ ss ++ as ++ cs
         where
          is | n == 0 = if c == C Z [S Z] then [(c,os)] else []
             | otherwise = go (n - 1) . (,CI:os) =<< intro c
          as = go n . (,CA:os) =<< app c
          ss = go n . (,CS:os) =<< shift c
          cs = go n . (,CC:os) =<< close c

termToLam :: [Op] -> String
termToLam xs = go ['a'..'z'] [] (reverse xs)
  where go (n:ns) cxt (CI:os) = ('(':'\\':n:'.':[]) ++ go ns (n:cxt) os
        go ns (v:cxt) (CS:os) = '[':v : go ns cxt os
        go ns (cxt) (CA:os) = ']': go ns cxt os -- halp
        go ns cxt (CC:os) = ")" ++ go ns cxt os
        go ns cxt [] = []
        go ns cxt os = error $ show (ns, cxt, os)

sgt = mapM_ putStrLn . map termToLam . map snd . genTerm

data FOL = Bind String FOL | App FOL FOL | Var String deriving Show

--termToFOL :: [OP] -> FOL
termToFOL xs =  snd $ go ['a'..'z'] [] [] (reverse xs)
  where go ns cxt [t] [] = (([],[],[],[]),t)
        go (n:ns) cxt tms (CI:os) =
                  let ((ns', cxt', tms', os'),body) =  go ns (n:cxt) [] os
                  -- should be cxt == cxt'
                  in go ns' cxt' (tms ++ [Bind (n:[]) body]) os'
        go ns (v:cxt) tms (CS:os) = go ns cxt (tms ++ [Var (v:[])]) os
        go ns (cxt) tms (CA:os) = case reverse tms of
                                       (t1:t2:ts) -> go ns cxt (reverse $ App t2 t1 :ts) os
        go ns cxt (t:[]) (CC:os) = ((ns,cxt,[],os),t)

        go ns cxt tms os = error $ show (ns, cxt, tms, os)


showFOL (Bind s x) = "\\"++s++"."++showFOL x
showFOL (App x y) = "("++showFOL x ++ ")(" ++ showFOL y ++ ")"
showFOL (Var s) = s

sft = mapM_ putStrLn . map showFOL . map termToFOL . map snd . genTerm