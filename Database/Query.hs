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

data Expr' r a l where
  Cnst :: Show a => l -> a -> Expr' r a l
  Sbst :: l -> String -> Expr' r a l
  Fld  :: l -> String -> (r -> a) -> Expr' r a l
  Fst  :: Show a => l -> Expr' r a l -> Expr' (r, s) a l
  Snd  :: Show a => l -> Expr' s a l -> Expr' (r, s) a l
  And  :: l -> Expr' r Bool l -> Expr' r Bool l -> Expr' r Bool l
  Grt  :: l -> Expr' r Int l -> Expr' r Int l -> Expr' r Bool l
  Plus :: l -> Expr' r Int l -> Expr' r Int l -> Expr' r Int l

deriving instance Functor (Expr' r a)
deriving instance Foldable (Expr' r a)
deriving instance Traversable (Expr' r a)

type Expr r a = Expr' r a ()
type LExpr r a = Expr' r a String

genVar :: State Int String
genVar = do
  i <- get
  modify (+1)
  return $ "a" ++ show i

labelExpr :: Expr r a -> LExpr r a
labelExpr expr = evalState (traverse (const genVar) expr) 0

brackets :: String -> String
brackets str = "(" ++ str ++ ")"

foldExprSql :: LExpr r a -> String
foldExprSql (Cnst _ a) = show a
foldExprSql (Sbst _ a) = a
foldExprSql (Fld l name _) = l ++ "." ++ name
foldExprSql (Fst _ e) = foldExprSql e
foldExprSql (Snd _ e) = foldExprSql e
foldExprSql (And _ a b) = brackets $ foldExprSql a ++ " and " ++ foldExprSql b
foldExprSql (Grt _ a b) = brackets $ foldExprSql a ++ " > " ++ foldExprSql b
foldExprSql (Plus _ a b) = brackets $ foldExprSql a ++ " + " ++ foldExprSql b

{-
cnst :: Show a => a -> Expr r a
cnst = Cnst ()

sbst = Sbst ()
fld = Fld ()
fst' = Fst ()
snd' = Snd ()
and = And ()
grt = Grt ()
plus = Plus ()

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

data QueryCache a = QueryCache [a]

data Query a where
  All    :: Row -> Query a
  Filter :: Expr a Bool -> Query a -> Query a
  Sort   :: Ord b => QueryCache a -> Label a b -> Maybe Int -> Query a -> Query a
  Join   :: Expr (a, b) Bool -> Query a -> Query b -> Query (a, b)

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

data Row = Row String

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
