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
  -- | forall s. Compose (Label r s) (Label s a)

data Expr r a where
  Cnst :: Show a => a -> Expr r a
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

queryLabel :: Query' a l -> l
queryLabel (All l _) = l
queryLabel (Filter l _ _) = l
queryLabel (Sort l _ _ _ _) = l
queryLabel (Join l _ _ _) = l

deriving instance Functor (Query' a)
deriving instance Foldable (Query' a)
deriving instance Traversable (Query' a)

labelQuery :: Query a -> LQuery a
labelQuery expr = evalState (traverse (const genVar) expr) 0

substFst :: Expr (l, r) a -> l -> Expr r a
substFst (Cnst a) sub = Cnst a
substFst (Fld _ _) sub = error "Invalid field access"
substFst (Fst f) sub = Cnst (foldExpr f sub)
substFst (Snd f) sub = f
substFst (And ql qr) sub = And (substFst ql sub) (substFst qr sub)
substFst (Grt ql qr) sub = Grt (substFst ql sub) (substFst qr sub)
substFst (Plus ql qr) sub = Plus (substFst ql sub) (substFst qr sub)

tee :: Expr (Person, Person) Bool
tee = Fst ageE `Grt` Snd ageE

foldExpr :: Expr r a -> (r -> a)
foldExpr (Cnst a) = const a
foldExpr (Fld _ get) = get
foldExpr (Fst f) = \(r, _) -> foldExpr f r
foldExpr (Snd f) = \(_, r) -> foldExpr f r
foldExpr (And a b) = \r -> foldExpr a r && foldExpr b r
foldExpr (Grt a b) = \r -> foldExpr a r > foldExpr b r
foldExpr (Plus a b) = \r -> foldExpr a r + foldExpr b r

--------------------------------------------------------------------------------

data Person = Person { _name :: String, _age :: Int }

name :: Label Person String
name = Label "name" _name

nameE :: Expr Person String
nameE = Fld "name" _name

age :: Label Person Int
age = Label "age" _age

ageE :: Expr Person Int
ageE = Fld "age" _age

expr :: Expr Person Bool
expr = (ageE `Plus` Cnst 5) `Grt` (Cnst 6)

te' :: Expr ((Person, Person), Person) Bool
te' = (Fst (Fst ageE) `Grt` (Snd ageE)) `And` (Fst (Snd ageE) `Grt` Cnst 6)

--------------------------------------------------------------------------------

foldQuerySql :: LQuery a -> String
foldQuerySql (All _ (Row row)) = "select * from " ++ row
foldQuerySql qq@(Filter l f q) = "select * from (" ++ foldQuerySql q ++ ") " ++ l ++ " where " ++ foldExprSql qq f
foldQuerySql qq@(Sort l _ (Label label _) limit q) = "select * from (" ++ foldQuerySql q ++ ") " ++ l ++ " order by " ++ l ++ "." ++ label ++ maybe "" ((" limit " ++) . show) limit
foldQuerySql qq@(Join _ f ql qr) = "select * from (" ++ foldQuerySql ql ++ ") " ++ queryLabel ql ++ " inner join (" ++ foldQuerySql qr ++") " ++ queryLabel qr ++ " on " ++ foldExprSql qq f

{-

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
