{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Database.Query where

import Control.Monad.State hiding (join)

import Data.Maybe
import Data.List                  (intersperse)
import Data.Ord

import qualified Data.ByteString.Char8 as B

import Data.Tree

import Prelude hiding (filter, sort, all, join)
import qualified Prelude as P

import qualified Database.PostgreSQL.Simple as PS
import qualified Database.PostgreSQL.Simple.Types as PS
import Database.PostgreSQL.Simple.Types ((:.)(..))
import qualified Database.PostgreSQL.Simple.FromRow as PS

import GHC.Generics

import Debug.Trace

insertBy' :: (a -> a -> Ordering) -> a -> [a] -> Int -> (Int, [a])
insertBy' _   x [] i = (i, [x])
insertBy' cmp x ys@(y:ys') i
 = case cmp x y of
     GT -> let (i', ys'') = insertBy' cmp x ys' (i + 1) in (i', y : ys'')
     _  -> (i, x : ys)

--------------------------------------------------------------------------------

-- NOTE: if we need to restrict the type of certain subexpressions, add a
-- phantom type, i.e.
-- data Expr tp r a where
--   Fld  :: String -> (r -> a) -> Expr Field r a

data Expr r a where
  Cnst :: Show a => a -> Expr r a
  Fld  :: String -> (r -> a) -> Expr r a
  Fst  :: Show a => Expr r a -> Expr (r :. s) a
  Snd  :: Show a => Expr s a -> Expr (r :. s) a
  And  :: Expr r Bool -> Expr r Bool -> Expr r Bool
  Grt  :: Expr r Int -> Expr r Int -> Expr r Bool
  Eqs  :: Expr r Int -> Expr r Int -> Expr r Bool
  Plus :: Expr r Int -> Expr r Int -> Expr r Int

instance Show (a -> b) where
  show _ = "(a -> b)"

deriving instance Show (Expr r a)

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

foldExprSql :: Ctx -> Expr r a -> String
foldExprSql ctx (Cnst a) = show a
foldExprSql ctx (Fld name _) = lookupVar ctx name
foldExprSql ctx (Fst q) = foldExprSql [ (ps, a, v) | (p, a, v) <- ctx, (F:ps) <- [p] ] q
foldExprSql ctx (Snd q) = foldExprSql [ (ps, a, v) | (p, a, v) <- ctx, (S:ps) <- [p] ] q
foldExprSql ctx (And a b) = brackets $ foldExprSql ctx a ++ " and " ++ foldExprSql ctx b
foldExprSql ctx (Grt a b) = brackets $ foldExprSql ctx a ++ " > " ++ foldExprSql ctx b
foldExprSql ctx (Eqs a b) = brackets $ foldExprSql ctx a ++ " = " ++ foldExprSql ctx b
foldExprSql ctx (Plus a b) = brackets $ foldExprSql ctx a ++ " + " ++ foldExprSql ctx b

data QueryCache a = QueryCache [a] deriving Show

data Row = Row String [String] deriving Show

data Query' a l where
  All    :: l -> Row -> Query' a l
  Filter :: l -> Expr a Bool -> Query' a l -> Query' a l
  Sort   :: Ord b => l -> QueryCache a -> Expr a b -> Maybe Int -> Query' a l -> Query' a l
  Join   :: (Show a, Show b) => l -> Expr (a :. b) Bool -> Query' a l -> Query' b l -> Query' (a :. b) l

deriving instance (Show l, Show a) => Show (Query' a l)

type Query a = Query' a ()
type LQuery a = Query' a String

all :: Row -> Query a
all = All ()

filter :: Expr a Bool -> Query a -> Query a
filter = Filter ()

sort :: Ord b => Expr a b -> Maybe Int -> Query a -> Query a
sort = Sort () (QueryCache [])

join :: (Show a, Show b) => Expr (a :. b) Bool -> Query a -> Query b -> Query (a :. b)
join = Join ()

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

substFst :: Expr (l :. r) a -> l -> Expr r a
substFst (Cnst a) sub = Cnst a
substFst (Fld _ _) sub = error "Invalid field access"
substFst (Fst f) sub = Cnst (foldExpr f sub)
substFst (Snd f) sub = f
substFst (And ql qr) sub = And (substFst ql sub) (substFst qr sub)
substFst (Grt ql qr) sub = Grt (substFst ql sub) (substFst qr sub)
substFst (Eqs ql qr) sub = Eqs (substFst ql sub) (substFst qr sub)
substFst (Plus ql qr) sub = Plus (substFst ql sub) (substFst qr sub)

substSnd :: Expr (l :. r) a -> r -> Expr l a
substSnd (Cnst a) sub = Cnst a
substSnd (Fld _ _) sub = error "Invalid field access"
substSnd (Fst f) sub = f
substSnd (Snd f) sub = Cnst (foldExpr f sub)
substSnd (And ql qr) sub = And (substSnd ql sub) (substSnd qr sub)
substSnd (Grt ql qr) sub = Grt (substSnd ql sub) (substSnd qr sub)
substSnd (Eqs ql qr) sub = Eqs (substSnd ql sub) (substSnd qr sub)
substSnd (Plus ql qr) sub = Plus (substSnd ql sub) (substSnd qr sub)

foldExpr :: Expr r a -> (r -> a)
foldExpr (Cnst a) = const a
foldExpr (Fld _ get) = get
foldExpr (Fst f) = \(r :. _) -> foldExpr f r
foldExpr (Snd f) = \(_ :. r) -> foldExpr f r
foldExpr (And a b) = \r -> foldExpr a r && foldExpr b r
foldExpr (Grt a b) = \r -> foldExpr a r > foldExpr b r
foldExpr (Eqs a b) = \r -> foldExpr a r == foldExpr b r
foldExpr (Plus a b) = \r -> foldExpr a r + foldExpr b r

--------------------------------------------------------------------------------

data Person = Person { _name :: String, _age :: Int } deriving (Generic, Show)

instance PS.FromRow Person

nameE :: Expr Person String
nameE = Fld "name" _name

ageE :: Expr Person Int
ageE = Fld "age" _age

expr :: Expr Person Bool
expr = (ageE `Plus` Cnst 5) `Grt` (Cnst 6)

-- te' :: Expr ((Person, Person), Person) Bool
te' = (Fst (Fst ageE) `Grt` (Snd ageE)) `And` (Fst (Snd ageE) `Grt` Cnst 6)

--------------------------------------------------------------------------------

aliasColumns :: String -> Ctx -> String
aliasColumns alias ctx = concat $ intersperse ", "
  [ case calias of
      Just calias' -> calias' ++ "_" ++ col ++ " as " ++ alias ++ "_" ++ calias' ++ "_" ++ col
      Nothing      -> col ++ " as " ++ alias ++ "_" ++ col
  | (_, calias, col) <- ctx
  ]

foldQuerySql :: LQuery a -> (String, Ctx)
foldQuerySql (All l (Row row cols)) =
  ( "select " ++ aliasColumns l ([ ([], Nothing, col) | col <- cols ]) ++ " from " ++ row
  , [ ([], Just l, col) | col <- cols ]
  )
foldQuerySql (Filter l f q) =
  ( "select " ++ aliasColumns l ctx ++ " from (" ++ q' ++ ") " ++ queryLabel q ++ " where " ++ foldExprSql ctx f
  , [ (p, Just $ maybe l (\a -> l ++ "_" ++ a) a, v) | (p, a, v) <- ctx ]
  )
  where (q', ctx) = foldQuerySql q
foldQuerySql (Sort l _ f limit q) =
  ( "select " ++ aliasColumns l ctx ++ " from (" ++ q' ++ ") " ++ queryLabel q ++ " order by " ++ foldExprSql ctx f  ++ maybe "" ((" limit " ++) . show) limit
  , [ (p, Just $ maybe l (\a -> l ++ "_" ++ a) a, v) | (p, a, v) <- ctx ]
  )
  where (q', ctx) = foldQuerySql q
foldQuerySql (Join l f ql qr) =
  ( "select " ++ aliasColumns l ctxl ++ ", " ++ aliasColumns l ctxr ++ " from (" ++ ql' ++ ") " ++ queryLabel ql ++ " inner join (" ++ qr' ++") " ++ queryLabel qr ++ " on " ++ foldExprSql ctx'' f
  , ctx'
  )
  where (ql', ctxl) = foldQuerySql ql
        (qr', ctxr) = foldQuerySql qr
        ctx' = [ (F:p, Just $ maybe l (\a -> l ++ "_" ++ a) a, v) | (p, a, v) <- ctxl ]
            ++ [ (S:p, Just $ maybe l (\a -> l ++ "_" ++ a) a, v) | (p, a, v) <- ctxr ]
        ctx'' = [ (F:p, a, v) | (p, a, v) <- ctxl ]
             ++ [ (S:p, a, v) | (p, a, v) <- ctxr ]

ql = (filter (ageE `Grt` Cnst 3) $ sort nameE (Just 10) $ filter (ageE `Grt` Cnst 6) $ all (Row "person" ["name", "age"]))
qr = all (Row "person" ["name", "age"])
-- q1 :: _
q1 = {- join (Fst ageE `Grt` Snd (Fst ageE)) ql -} (join (Fst ageE `Grt` Snd ageE) ql qr)

q1sql = fst $ foldQuerySql (labelQuery q1)

-- q2 :: _ -- Query ((Person, Person), Person)
q2 = sort (Fst (Fst ageE)) (Just 100) $ join ((Fst (Fst ageE) `Grt` Fst (Snd ageE)) `And` (Fst (Fst ageE) `Grt` Cnst 666)) (join (Fst ageE `Grt` Snd ageE) allPersons allPersons) (join (Fst (Fst ageE) `Grt` Snd ageE) (join (Fst ageE `Grt` Snd ageE) allPersons allPersons) allPersons)

q2sql = fst $ foldQuerySql (labelQuery q2)

allPersons = all (Row "person" ["name", "age"])

simplejoin = join (Fst ageE `Eqs` Snd ageE) allPersons allPersons
simplejoinsql = fst $ foldQuerySql (labelQuery simplejoin)

simplejoinsbstsql = fst $ foldQuerySql $ labelQuery $ filter (substFst (Fst ageE `Grt` Snd ageE) (Person "name" 666)) allPersons

simple = filter (ageE `Grt` Cnst 7) $ filter (ageE `Grt` Cnst 7) $ {- join (Fst ageE `Grt` Snd ageE) allPersons -} (filter (ageE `Grt` Cnst 6) allPersons)
simplesql = fst $ foldQuerySql (labelQuery simple)

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
-}

data Index a = Unknown | Index Int
data SortOrder a = forall b. Ord b => SortBy (Expr a b) | Unsorted

fromRow :: Row -> Maybe a
fromRow = undefined

updateCache :: Ord b => QueryCache a -> Expr a b -> Maybe Int -> a -> IO (Maybe (Index a))
updateCache = undefined

requestFromDb :: String -> IO [a]
requestFromDb = undefined

-- TODO: return sort expr too

passesQuery :: Query a -> Row -> IO (SortOrder a, [(Index a, a)])
passesQuery (All _ (Row _ r')) row@(Row _ r) = if r == r'
  then case fromRow row of
    Just a -> return (Unsorted, [(Unknown, a)])
    _      -> return (Unsorted, [])
  else return (Unsorted, [])
passesQuery (Filter _ f q) row = do
  rs <- passesQuery q row
  return (fst rs, P.filter (foldExpr f . snd) $ snd rs)
passesQuery (Sort _ cache label limit q) row = do
  rs <- passesQuery q row
  rs' <- forM (snd rs) $ \(_, r) -> do
    index <- updateCache cache label limit r
    return ((,r) <$> index)
  return (SortBy label, catMaybes rs')
passesQuery (Join _ f ql qr) row = do
  rl <- passesQuery ql row
  rr <- passesQuery qr row
  rl' <- forM (snd rl) $ \(_, r) -> do
    ls <- requestFromDb $ fst $ foldQuerySql $ labelQuery $ filter (substFst f r) qr
    return [ (Unknown, (r :. l)) | l <- ls ]
  rr' <- forM (snd rr) $ \(_, r) -> do
    ls <- requestFromDb $ fst $ foldQuerySql $ labelQuery $ filter (substSnd f r) ql
    return [ (Unknown, (l :. r)) | l <- ls ]
  return (Unsorted, concat rl' ++ concat rr')

query :: PS.FromRow a => PS.Connection -> Query a -> IO [a]
query conn q = do
  rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery q)
  return rs

test :: IO ()
test = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"
  rs <- query conn simplejoin
  print rs
  return ()

--------------------------------------------------------------------------------
