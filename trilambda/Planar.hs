{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Planar where

-- for each variable introduced, after the application (or introduction) of which term is it introduced. so a backedge, for each n, some m < n, with no crossing

{-
type Planar = [Int]

planars1 = 0 : (ma

-}

data Nat = Z | S Nat deriving (Read, Show)

data Planar (a :: Nat) where
   BindL :: Planar a -> Planar a
   BindR :: Planar a -> Planar a
   BindAppL  :: Planar (S a) -> Planar a -> Planar a
   BindAppR  :: Planar a -> Planar S a -> Planar a
   PID :: Planar Z
   Var :: Planar (S a)