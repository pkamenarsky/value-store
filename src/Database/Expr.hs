{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Database.Expr where

import Control.Monad hiding (join)
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

instance Show (Expr r a) where
  show ((:+:) e1 e2) = show e1 ++ "." ++ show e2
  show (Cnst a)      = show a
  show (Fld fld _)   = fld
  show (Fst e)       = show e
  show (Snd e)       = show e
  -- show (Fst e)       = "fst " ++ brackets (show e)
  -- show (Snd e)       = "snd " ++ brackets (show e)
  show (And e1 e2)   = show e1 ++ " ∧ " ++ show e2
  show (Grt e1 e2)   = show e1 ++ " > " ++ show e2
  show (Eqs e1 e2)   = show e1 ++ " ≡ " ++ show e2
  show (Plus e1 e2)  = show e1 ++ " + " ++ show e2

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

substFst :: Expr (l :. r) a -> l -> Maybe (Expr r a)
substFst (Cnst a) sub = Just $ Cnst a
substFst (Fld _ _) sub = error "Invalid field access"
substFst (_ :+: _ ) sub = error "Invalid field access"
substFst (Fst f) sub = Cnst <$> foldExpr f sub
substFst (Snd f) sub = Just f
substFst (And ql qr) sub  = And  <$> substFst ql sub <*> substFst qr sub
substFst (Grt ql qr) sub  = Grt  <$> substFst ql sub <*> substFst qr sub
substFst (Eqs ql qr) sub  = Eqs  <$> substFst ql sub <*> substFst qr sub
substFst (Plus ql qr) sub = Plus <$> substFst ql sub <*> substFst qr sub

substSnd :: Expr (l :. r) a -> r -> Maybe (Expr l a)
substSnd (Cnst a) sub = Just $ Cnst a
substSnd (Fld _ _) sub = error "Invalid field access"
substSnd (_ :+: _ ) sub = error "Invalid field access"
substSnd (Fst f) sub = Just f
substSnd (Snd f) sub = Cnst <$> foldExpr f sub
substSnd (And ql qr) sub  = And  <$> (substSnd ql sub) <*> (substSnd qr sub)
substSnd (Grt ql qr) sub  = Grt  <$> (substSnd ql sub) <*> (substSnd qr sub)
substSnd (Eqs ql qr) sub  = Eqs  <$> (substSnd ql sub) <*> (substSnd qr sub)
substSnd (Plus ql qr) sub = Plus <$> (substSnd ql sub) <*> (substSnd qr sub)

foldExpr :: Expr r a -> (r -> Maybe a)
foldExpr (Cnst a) = const $ Just a
foldExpr (Fld _ get) = get
foldExpr (f :+: g) = foldExpr g <=< foldExpr f
foldExpr (Fst f) = \(r :. _) -> foldExpr f r
foldExpr (Snd f) = \(_ :. r) -> foldExpr f r
foldExpr (And a b) = \r -> (&&) <$> foldExpr a r <*> foldExpr b r
foldExpr (Grt a b) = \r -> (>)  <$> foldExpr a r <*> foldExpr b r
foldExpr (Eqs a b) = \r -> (==) <$> foldExpr a r <*> foldExpr b r
foldExpr (Plus a b) = \r -> (+) <$> foldExpr a r <*> foldExpr b r

keyE :: Expr a String
keyE = Fld "key" (error "keyE can be used only live")
