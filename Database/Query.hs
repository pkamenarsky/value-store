{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

module Database.Query where

import Control.Monad.State

import Data.Ord

insertBy' :: (a -> a -> Ordering) -> a -> [a] -> Int -> (Int, [a])
insertBy' _   x [] i = (i, [x])
insertBy' cmp x ys@(y:ys') i
 = case cmp x y of
     GT -> let (i', ys'') = insertBy' cmp x ys' (i + 1) in (i', y : ys'')
     _  -> (i, x : ys)

--------------------------------------------------------------------------------

data Label r a =
    Label String (r -> a)
  | forall s. Compose (Label r s) (Label s a)

data First
data Second

data Expr r a where
  Cnst :: Show a => a -> Expr r a
  Sbst :: String -> Expr r a
  Fld  :: Label r a -> Expr r a
  Fst  :: Label r a -> Expr (r, s) a
  Snd  :: Label s a -> Expr (r, s) a
  And  :: Expr r Bool -> Expr r Bool -> Expr r Bool
  Grt  :: Expr r Int -> Expr r Int -> Expr r Bool
  Plus :: Expr r Int -> Expr r Int -> Expr r Int

substFst :: Expr (l, r) a -> String -> Expr r a
substFst (Cnst a) sub = Cnst a
substFst (Fld a) sub = error "Invalid field access"
substFst (Fst a) sub = Sbst sub
substFst (Snd a) sub = Fld a
substFst (And ql qr) sub = And (substFst ql sub) (substFst qr sub)

tee :: Expr (Person, Person) Bool
tee = Fst age `Grt` Snd age

foldExpr :: Expr r a -> (r -> a)
foldExpr (Cnst a) = const a
foldExpr (Fld (Label _ get)) = get
foldExpr (And a b) = \r -> foldExpr a r && foldExpr b r
foldExpr (Grt a b) = \r -> foldExpr a r > foldExpr b r
foldExpr (Plus a b) = \r -> foldExpr a r + foldExpr b r

brackets :: String -> String
brackets str = "(" ++ str ++ ")"

type Ctx = (String, String, String)

foldExprSql :: Ctx -> Expr r a -> String
foldExprSql ctx (Cnst a) = show a
foldExprSql (var, _, _) (Fld (Label name _)) = var ++ "." ++ name
foldExprSql (_, fst, _) (Fst (Label name _)) = fst ++ "." ++ name
foldExprSql (_, _, snd) (Snd (Label name _)) = snd ++ "." ++ name
foldExprSql ctx (And a b) = brackets $ foldExprSql ctx a ++ " and " ++ foldExprSql ctx b
foldExprSql ctx (Grt a b) = brackets $ foldExprSql ctx a ++ " > " ++ foldExprSql ctx b
foldExprSql ctx (Plus a b) = brackets $ foldExprSql ctx a ++ " + " ++ foldExprSql ctx b

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

{-
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
-}

data QueryCache a = QueryCache [a]

data Query a where
  All    :: Row -> Query a
  Filter :: Expr a Bool -> Query a -> Query a
  Sort   :: Ord b => QueryCache a -> Label a b -> Maybe Int -> Query a -> Query a
  JoinEq :: Eq r => Label a r -> Label b r -> Query a -> Query b -> Query (a, b)
  Join   :: Expr (a, b) Bool -> Query a -> Query b -> Query (a, b)

type Var = State Int

genVar :: Var String
genVar = do
  i <- get
  modify (+1)
  return $ "a" ++ show i

retrieveSql :: Query a -> [a]
retrieveSql = undefined

foldQuerySql :: Query a -> Var String
foldQuerySql (All (Row row)) = return $ "select * from " ++ row
foldQuerySql (Filter f q) = do
  var <- genVar
  fq <- foldQuerySql q
  return $ "select * from (" ++ fq ++ ") " ++ var ++ " where " ++ foldExprSql (var, "fst", "snd") f
foldQuerySql (Sort _ (Label label _) limit q) = do
  var <- genVar
  fq <- foldQuerySql q
  return $ "select * from (" ++ fq ++ ") " ++ var ++ " order by " ++ var ++ "." ++ label ++ maybe "" ((" limit " ++) . show) limit
foldQuerySql (Join f ql qr) = do
  varl <- genVar
  varr <- genVar
  fql <- foldQuerySql ql
  fqr <- foldQuerySql qr
  return $ "select * from (" ++ fql ++ ") " ++ varl ++ " inner join (" ++ fqr ++") " ++ varr ++ " on " ++ foldExprSql ("var", varl, varr) f

q1 = Join (Fst age `Grt` Snd age) (Filter (ageE `Grt` Cnst 6) $ Sort undefined name (Just 10) $ Filter (ageE `Grt` Cnst 6) $ All (Row "person")) (All (Row "person"))

q1sql :: String
q1sql = evalState (foldQuerySql q1) 0

data Index a = Unknown | Index Int

data Row = Row String

fromRow :: Row -> Maybe a
fromRow = undefined

updateCache :: Ord b => QueryCache a -> Label a b -> Maybe Int -> a -> IO (Maybe (Index a))
updateCache = undefined

passesQuery :: Query a -> QueryCache a -> Row -> IO (Maybe (Index a, a))
passesQuery (All (Row r')) _ row@(Row r) = if r == r'
  then case fromRow row of
    Just a -> return (Just (Unknown, a))
    _      -> return Nothing
  else return Nothing
passesQuery (Filter f q) cache row = do
  r <- passesQuery q cache row
  case r of
    Nothing -> return Nothing
    Just (_, a)  -> if foldExpr f a
      then return (Just (Unknown, a))
      else return Nothing
passesQuery (Sort cache label limit q) _ row = do
  r <- passesQuery q cache row
  case r of
    Nothing -> return Nothing
    Just (_, a) -> do
      index <- updateCache cache label limit a
      return ((,a) <$> index)
passesQuery (JoinEq (Label _ ll) (Label _ lr) ql qr) (QueryCache xs) row = do
  r <- passesQuery ql (QueryCache $ map fst xs) row -- pass cache like that good?
  case r of
    Nothing -> return Nothing
    Just (_, a) -> do
      let r' = [ (a, b) | (_, b) <- xs, ll a == lr b ]
      return undefined
passesQuery (Join f ql qr) (QueryCache xs) row = do
  rl <- passesQuery ql (QueryCache $ map fst xs) row
  rr <- passesQuery qr (QueryCache $ map snd xs) row
  case (rl, rr) of
    (Just (_, a), Nothing) -> do
      let sql = Filter (substFst f "") qr
      return undefined
  return undefined

--------------------------------------------------------------------------------
