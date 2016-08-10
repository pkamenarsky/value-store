{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module Database.Query where

import Control.Monad.State

import Data.Maybe
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

data Expr r a where
  Cnst :: Show a => a -> Expr r a
  Sbst :: String -> Expr r a
  Fld  :: String -> (r -> a) -> Expr r a
  Fst  :: Show a => Expr r a -> Expr (r, s) a
  Snd  :: Show a => Expr s a -> Expr (r, s) a
  And  :: Expr r Bool -> Expr r Bool -> Expr r Bool
  Grt  :: Expr r Int -> Expr r Int -> Expr r Bool
  Plus :: Expr r Int -> Expr r Int -> Expr r Int

genVar :: State Int String
genVar = do
  i <- get
  modify (+1)
  return $ "a" ++ show i

brackets :: String -> String
brackets str = "(" ++ str ++ ")"

foldExprSql :: LQuery b -> Expr r a -> String
foldExprSql q (Cnst a) = show a
foldExprSql q (Sbst a) = a

foldExprSql (All l _) (Fld name _) = l ++ "." ++ name
foldExprSql (Filter l _ _) (Fld name _) = l ++ "." ++ name
foldExprSql (Sort l _ _ _ _) (Fld name _) = l ++ "." ++ name
foldExprSql (Join l _ _ _) (Fld name _) = error "Fld on Join"

foldExprSql (Join _ _ ql qr) (Fst e) = foldExprSql ql e
foldExprSql _ (Fst e) = "Fst not on Join"

foldExprSql (Join _ _ ql qr) (Snd e) = foldExprSql qr e
foldExprSql _ (Snd e) = "Snd not on Join"

foldExprSql q (And a b) = brackets $ foldExprSql q a ++ " and " ++ foldExprSql q b
foldExprSql q (Grt a b) = brackets $ foldExprSql q a ++ " > " ++ foldExprSql q b
foldExprSql q (Plus a b) = brackets $ foldExprSql q a ++ " + " ++ foldExprSql q b

data QueryCache a = QueryCache [a]

data Row = Row String

data Query' a l where
  All    :: l -> Row -> Query' a l
  Filter :: l -> Expr a Bool -> Query' a l -> Query' a l
  Sort   :: Ord b => l -> QueryCache a -> Label a b -> Maybe Int -> Query' a l -> Query' a l
  Join   :: l -> Expr (a, b) Bool -> Query' a l -> Query' b l -> Query' (a, b) l

type Query a = Query' a ()
type LQuery a = Query' a String

deriving instance Functor (Query' a)
deriving instance Foldable (Query' a)
deriving instance Traversable (Query' a)

labelQuery :: Query a -> LQuery a
labelQuery expr = evalState (traverse (const genVar) expr) 0

{-
substFst :: Expr (l, r) a -> l -> Expr r a
substFst (Cnst _ a) sub = Cnst () a
substFst (Fld _ a) sub = error "Invalid field access"
substFst (Fst _ (Label _ get)) sub = Sbst () (show $ get sub)
substFst (Fst' _ f) sub = Sbst () (show $ foldExpr f sub)
substFst (Snd _ a) sub = Fld () a
substFst (Snd' _ f) sub = f
substFst (And _ ql qr) sub = And () (substFst ql sub) (substFst qr sub)
substFst (Grt _ ql qr) sub = Grt () (substFst ql sub) (substFst qr sub)
substFst (Plus _ ql qr) sub = Plus () (substFst ql sub) (substFst qr sub)

tee :: Expr (Person, Person) Bool
tee = Fst age `Grt` Snd age

foldExpr :: Expr r a -> (r -> a)
foldExpr (Cnst a) = const a
foldExpr (Fld (Label _ get)) = get
foldExpr (And a b) = \r -> foldExpr a r && foldExpr b r
foldExpr (Grt a b) = \r -> foldExpr a r > foldExpr b r
foldExpr (Plus a b) = \r -> foldExpr a r + foldExpr b r

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

ageE' :: Expr Person Int
ageE' = Fld' "age" _age

expr :: Expr Person Bool
expr = (ageE `Plus` Cnst 5) `Grt` (Cnst 6)

te' :: Expr ((Person, Person), Person) Bool
te' = (Fst' (Fst' ageE') `Grt` (Snd' ageE)) `And` (Fst' (Snd' ageE') `Grt` Cnst 6)

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

ql = (Filter (ageE `Grt` Cnst 6) $ Sort undefined name (Just 10) $ Filter (ageE `Grt` Cnst 6) $ All (Row "person"))
qr = All (Row "person")
q1 = Join (Fst age `Grt` Snd age) ql qr

subsql = substFst (Fst age `Grt` Snd age) (Person "asd" 6)
subsqlSql = foldExprSql ("var", "fst", "snd") subsql

q1sql :: String
q1sql = evalState (foldQuerySql q1) 0

data Index a = Unknown | Index Int

fromRow :: Row -> Maybe a
fromRow = undefined

updateCache :: Ord b => QueryCache a -> Label a b -> Maybe Int -> a -> IO (Maybe (Index a))
updateCache = undefined

requestFromDb :: String -> IO [a]
requestFromDb = undefined

passesQuery :: Query a -> Row -> IO [(Index a, a)]
passesQuery (All (Row r')) row@(Row r) = if r == r'
  then case fromRow row of
    Just a -> return [(Unknown, a)]
    _      -> return []
  else return []
passesQuery (Filter f q) row = do
  rs <- passesQuery q row
  return $ filter (foldExpr f . snd) rs
passesQuery (Sort cache label limit q) row = do
  rs <- passesQuery q row
  rs' <- forM rs $ \(_, r) -> do
    index <- updateCache cache label limit r
    return ((,r) <$> index)
  return $ catMaybes rs'
passesQuery (Join f ql qr) row = do
  rl <- passesQuery ql row
  rr <- passesQuery qr row
  rs' <- forM rl $ \(_, r) -> do
    ls <- requestFromDb $ evalState (foldQuerySql $ Filter (substFst f r) qr) 0
    return [ (Unknown, (r, l)) | l <- ls ]
  return $ concat rs'

--------------------------------------------------------------------------------
-}
