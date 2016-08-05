{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}

module Database.Query where

import Data.Ord

insertBy' :: (a -> a -> Ordering) -> a -> [a] -> Int -> (Int, [a])
insertBy' _   x [] i = (i, [x])
insertBy' cmp x ys@(y:ys') i
 = case cmp x y of
     GT -> let (i', ys'') = insertBy' cmp x ys' (i + 1) in (i', y : ys'')
     _  -> (i, x : ys)

--------------------------------------------------------------------------------

data Label r a = Label String (r -> a)

data Expr r a where
  Cnst :: Show a => a -> Expr r a
  Fld  :: Label r a -> Expr r a
  And  :: Expr r Bool -> Expr r Bool -> Expr r Bool
  Grt  :: Expr r Int -> Expr r Int -> Expr r Bool
  Plus :: Expr r Int -> Expr r Int -> Expr r Int

foldExpr :: Expr r a -> (r -> a)
foldExpr (Cnst a) = const a
foldExpr (Fld (Label _ get)) = get
foldExpr (And a b) = \r -> foldExpr a r && foldExpr b r
foldExpr (Grt a b) = \r -> foldExpr a r > foldExpr b r
foldExpr (Plus a b) = \r -> foldExpr a r + foldExpr b r

brackets :: String -> String
brackets str = "(" ++ str ++ ")"

foldExprSql :: Expr r a -> String
foldExprSql (Cnst a) = show a
foldExprSql (Fld (Label name _)) = name
foldExprSql (And a b) = brackets $ foldExprSql a ++ " and " ++ foldExprSql b
foldExprSql (Grt a b) = brackets $ foldExprSql a ++ " > " ++ foldExprSql b
foldExprSql (Plus a b) = brackets $ foldExprSql a ++ " + " ++ foldExprSql b

--------------------------------------------------------------------------------

data Person = Person { _name :: String, _age :: Int }

name :: Label Person String
name = Label "name" _name

nameE :: Expr Person String
nameE = Fld name

age :: Label Person Int
age = Label "age" _age

ageE :: Expr Person Int
ageE = Fld age

expr :: Expr Person Bool
expr = (ageE `Plus` Cnst 5) `Grt` (Cnst 6)

--------------------------------------------------------------------------------

data Limit a = forall r. Ord r => Limit (Label a r) Int | NoLimit

data Query a = Query [a] (a -> Bool) (Limit a)

-- Returns the index of the new record.
triggersQuery :: Query a -> a -> Maybe (Query a, Int)
triggersQuery (Query xs flr limit) x
  | not (flr x)              = Nothing
  | NoLimit         <- limit = Just (Query [] flr NoLimit, 0)
  | Limit (Label _ get) count <- limit
  , (pos, xs')      <- insertBy' (comparing get) x xs 0 = if pos < count
      then Just (Query (take count xs') flr limit, pos)
      else Nothing

--------------------------------------------------------------------------------
