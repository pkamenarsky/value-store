{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Database.Expr where

import Data.Functor.Foldable

import Database.PostgreSQL.Simple.Types ((:.)(..))

data Expr' r a expr where
  (:+:) :: expr a c -> expr a c -> Expr' a c expr
  {-
  Cnst  :: Show a => a -> Expr' r a expr
  Fld   :: String -> (r -> Maybe a) -> Expr' r a expr
  Fst   :: expr r a -> Expr' (r :. s) a expr
  Snd   :: expr s a -> Expr' (r :. s) a expr
  And   :: expr r Bool -> expr r Bool -> Expr' r Bool expr
  Grt   :: Ord a => expr r a -> expr r a -> Expr' r Bool expr
  Eqs   :: Eq  a => expr r a -> expr r a -> Expr' r Bool expr
  Plus  :: Num n => expr r n -> expr r n -> Expr' r n expr
  -}

type Expr r a = Fix (Expr' r a)

-- deriving instance Functor (Expr' r a)

{-
data A' a e = A a e | B a e

deriving instance Functor (A a)

data A a = Fix (A' a a)
-}

foldA :: Expr r a -> (r -> Maybe a)
foldA = undefined -- cata f
  where f = undefined

foldExpr :: Expr r a -> (r -> Maybe a)
foldExpr = cata f
  where f = undefined
