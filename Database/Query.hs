{-# LANGUAGE GADTs #-}

module Database.Query where

data Limit a = Limit (a -> a -> Ordering) Int | NoLimit

data Query a = Query [a] (a -> Bool) (Limit a)

-- Returns the index of the new record.
triggersQuery :: Query a -> a -> Maybe (Query a, Int)
triggersQuery (Query xs flr limit) x
  | not (flr x)              = Nothing
  | NoLimit         <- limit = Just (Query [] flr NoLimit, 0)
  | Limit srt count <- limit
  , (pos, xs')      <- insertBy' srt x xs 0 = if pos < count
      then Just (Query (take count xs') flr limit, pos)
      else Nothing

--------------------------------------------------------------------------------

insertBy' :: (a -> a -> Ordering) -> a -> [a] -> Int -> (Int, [a])
insertBy' _   x [] i = (i, [x])
insertBy' cmp x ys@(y:ys') i
 = case cmp x y of
     GT -> let (i', ys'') = insertBy' cmp x ys' (i + 1) in (i', y : ys'')
     _  -> (i, x : ys)

--------------------------------------------------------------------------------

data Expr r a where
  Cnst :: a -> Expr r a
  Fld  :: String -> (r -> a) -> Expr r a
  And  :: Expr r Bool -> Expr r Bool -> Expr r Bool
  Grt  :: Expr r Int -> Expr r Int -> Expr r Bool
  Plus :: Expr r Int -> Expr r Int -> Expr r Int

foldExpr :: Expr r a -> (r -> a)
foldExpr (Cnst a) = const a
foldExpr (Fld _ get) = get
foldExpr (And a b) = \r -> foldExpr a r && foldExpr b r
foldExpr (Grt a b) = \r -> foldExpr a r > foldExpr b r
foldExpr (Plus a b) = \r -> foldExpr a r + foldExpr b r

--------------------------------------------------------------------------------

data Person = Person { _name :: String, _age :: Int }

name :: Expr Person String
name = Fld "name" _name

age :: Expr Person Int
age = Fld "age" _age

expr :: Expr Person Bool
expr = (age `Plus` Cnst 5) `Grt` (Cnst 6)
