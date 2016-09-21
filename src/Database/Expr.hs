{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Database.Expr where

import Control.Monad.Trans.State.Strict
import qualified Data.List        as L

import Database.PostgreSQL.Simple.Types ((:.)(..))

genVar :: State Int String
genVar = do
  i <- get
  modify (+1)
  return $ "a" ++ show i

brackets :: String -> String
brackets str = "(" ++ str ++ ")"

data Path = F | S deriving (Show, Eq)

type Ctx = [([Path], Maybe String, String)]

lookupVar :: Ctx -> String -> String
lookupVar ctx name =
  case [ (a, v) | (p, a, v) <- ctx, name == v, p == [] ] of
    [(Just alias, var)] -> alias ++ "_" ++ var
    [(Nothing, var)]    -> var
    []                  -> error "No such var"
    _                   -> error "More than one var"

class ToExpr r a where

data Expr r a where
  (:+:) :: Expr a b -> Expr b c -> Expr a c
  Cnst  :: Show a => a -> Expr r a
  Fld   :: String -> (r -> Maybe a) -> Expr r a
  Fst   :: Show a => Expr r a -> Expr (r :. s) a
  Snd   :: Show a => Expr s a -> Expr (r :. s) a
  And   :: Expr r Bool -> Expr r Bool -> Expr r Bool
  Grt   :: Ord a => Expr r a -> Expr r a -> Expr r Bool
  Eqs   :: Eq  a => Expr r a -> Expr r a -> Expr r Bool
  Plus  :: Num n => Expr r n -> Expr r n -> Expr r n

foldExprSql :: Ctx -> Expr r a -> String
-- TODO: FIXME
foldExprSql ctx (Cnst a) = "'" ++ (L.filter (/= '\"') $ show a) ++ "'"
foldExprSql ctx (Fld name _) = lookupVar ctx name
foldExprSql ctx (Fld name _ :+: Fld name' _) = lookupVar ctx (name ++ "_" ++ name')
foldExprSql ctx (_ :+: _) = "Can compose only fields"
foldExprSql ctx (Fst q) = foldExprSql [ (ps, a, v) | (p, a, v) <- ctx, (F:ps) <- [p] ] q
foldExprSql ctx (Snd q) = foldExprSql [ (ps, a, v) | (p, a, v) <- ctx, (S:ps) <- [p] ] q
foldExprSql ctx (And a b) = brackets $ foldExprSql ctx a ++ " and " ++ foldExprSql ctx b
foldExprSql ctx (Grt a b) = brackets $ foldExprSql ctx a ++ " > " ++ foldExprSql ctx b
foldExprSql ctx (Eqs a b) = brackets $ foldExprSql ctx a ++ " = " ++ foldExprSql ctx b
foldExprSql ctx (Plus a b) = brackets $ foldExprSql ctx a ++ " + " ++ foldExprSql ctx b
