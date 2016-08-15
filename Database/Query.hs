{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Database.Query where

import Control.Monad.State hiding (join)
import Control.Concurrent

import qualified Data.Aeson as A

import Data.Char
import Data.Data
import Data.IORef
import Data.Maybe
import Data.List                  (intersperse)
import Data.Ord

import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy as BL

import Data.Tree

import Prelude hiding (filter, sort, all, join)
import qualified Prelude as P

import qualified Database.PostgreSQL.Simple as PS
import qualified Database.PostgreSQL.Simple.Types as PS
import qualified Database.PostgreSQL.Simple.ToField as PS
import qualified Database.PostgreSQL.Simple.ToRow as PS
import qualified Database.PostgreSQL.Simple.Notification as PS
import Database.PostgreSQL.Simple.Types ((:.)(..))
import qualified Database.PostgreSQL.Simple.FromRow as PS

import System.IO.Unsafe

import GHC.Generics
import Database.Generic

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

instance Show (IORef a) where
  show _ = "IORef _"

data QueryCache a = QueryCache (Maybe (IORef [a])) deriving Show

data Row = Row String [String] deriving Show

data DBValue = DBValue String A.Value

data Query' a l where
  All    :: A.FromJSON a => l -> Row -> Query' a l
  Filter :: l -> Expr a Bool -> Query' a l -> Query' a l
  Sort   :: (Ord b, PS.FromRow a) => l -> QueryCache a -> Expr a b -> Maybe Int -> Query' a l -> Query' a l
  Join   :: (Show a, Show b, PS.FromRow a, PS.FromRow b) => l -> Expr (a :. b) Bool -> Query' a l -> Query' b l -> Query' (a :. b) l

deriving instance (Show l, Show a) => Show (Query' a l)

type Query a = Query' a ()
type LQuery a = Query' a String

all :: A.FromJSON a => Row -> Query a
all = All ()

filter :: Expr a Bool -> Query a -> Query a
filter = Filter ()

sort :: (Ord b, PS.FromRow a) => Expr a b -> Maybe Int -> Query a -> Query a
sort = Sort () (QueryCache Nothing)

join :: (Show a, Show b, PS.FromRow a, PS.FromRow b) => Expr (a :. b) Bool -> Query a -> Query b -> Query (a :. b)
join = Join ()

queryLabel :: Query' a l -> l
queryLabel (All l _) = l
queryLabel (Filter l _ _) = l
queryLabel (Sort l _ _ _ _) = l
queryLabel (Join l _ _ _) = l

deriving instance Functor (Query' a)
deriving instance Foldable (Query' a)
deriving instance Traversable (Query' a)

labelQuery :: Query' a l -> LQuery a
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

data Person = Person { _name :: String, _age :: Int } deriving (Generic, Typeable, Data, Show)

data Address = Address { _street :: String, _person :: Person } deriving (Generic, Typeable, Data, Show)

instance PS.FromRow Person
instance PS.ToRow Person

instance A.FromJSON Person
instance A.ToJSON Person

instance DBRow Person
instance Fields Person
instance DBRow Address
instance Fields Address

data Image = Horizontal | Vertical Person String deriving Generic

instance DBRow Image
instance Fields Image

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

simplejoin = sort (Fst ageE) (Just 100) $ join (Fst ageE `Eqs` Snd ageE) allPersons allPersons
simplejoinsql = fst $ foldQuerySql (labelQuery simplejoin)

simplejoinsbstsql = fst $ foldQuerySql $ labelQuery $ filter (substFst (Fst ageE `Grt` Snd ageE) (Person "name" 666)) allPersons

simple = filter (ageE `Grt` Cnst 7) $ filter (ageE `Grt` Cnst 7) $ {- join (Fst ageE `Grt` Snd ageE) allPersons -} (filter (ageE `Grt` Cnst 6) allPersons)
simplesql = fst $ foldQuerySql (labelQuery simple)

data Index a = Unknown | Index Int deriving Show
data SortOrder a = forall b. Ord b => SortBy (Expr a b) | Unsorted

deriving instance Show (SortOrder a)

updateCache :: Ord b => QueryCache a -> Expr a b -> Maybe Int -> a -> IO (Maybe (Index a))
updateCache (QueryCache _) f Nothing a                 = return (Just Unknown)
updateCache (QueryCache Nothing) f (Just limit) a      = error "No cache"
updateCache (QueryCache (Just cache)) f (Just limit) a = do
  rs <- readIORef cache
  let (i, rs') = insertBy' (comparing (foldExpr f)) a rs 0
  writeIORef cache (take limit rs')
  if i < limit
    then return (Just (Index i))
    else return Nothing

passesQuery :: PS.Connection -> LQuery a -> DBValue -> IO (SortOrder a, [(Index a, a)])
passesQuery conn (All _ (Row r' _)) row@(DBValue r value) = if r == r'
  then case A.fromJSON value of
    A.Success a -> return (Unsorted, [(Unknown, a)])
    _           -> return (Unsorted, [])
  else return (Unsorted, [])
passesQuery conn (Filter _ f q) row = do
  rs <- passesQuery conn q row
  return (fst rs, P.filter (foldExpr f . snd) $ snd rs)
passesQuery conn (Sort _ cache label limit q) row = do
  rs <- passesQuery conn q row
  rs' <- forM (snd rs) $ \(_, r) -> do
    index <- updateCache cache label limit r
    return ((,r) <$> index)
  return (SortBy label, catMaybes rs')
passesQuery conn (Join _ f ql qr) row = do
  rl <- passesQuery conn ql row
  rr <- passesQuery conn qr row
  if not (null rl)
    then do
      rl' <- forM (snd rl) $ \(_, r) -> do
        ls <- PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ filter (substFst f r) $ fmap (const ()) qr
        -- print $ fst $ foldQuerySql $ labelQuery $ filter (substFst f r) qr
        return [ (Unknown, (r :. l)) | l <- ls ]
      return (Unsorted, concat rl')
    else do
      rr' <- forM (snd rr) $ \(_, r) -> do
        ls <- PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ filter (substSnd f r) $ fmap (const ()) ql
        -- print $ fst $ foldQuerySql $ labelQuery $ filter (substSnd f r) ql
        return [ (Unknown, (l :. r)) | l <- ls ]
      return (Unsorted, concat rr')

fillCaches :: PS.Connection -> LQuery a -> IO (LQuery a)
fillCaches _ (All l a) = return (All l a)
fillCaches conn (Filter l a q) = do
  q' <- fillCaches conn q
  return (Filter l a q')
fillCaches conn qq@(Sort l _ b limit q) = do
  cache <- case limit of
    Just _  -> do
      rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql qq)
      QueryCache . Just <$> newIORef rs
    Nothing -> return $ QueryCache Nothing
  q' <- fillCaches conn q
  return (Sort l cache b limit q')
fillCaches conn (Join l a ql qr) = do
  ql' <- fillCaches conn ql
  qr' <- fillCaches conn qr
  return (Join l a ql' qr')

listen :: (String -> A.Value -> IO ()) -> IO ()
listen = undefined

insertRow :: (A.ToJSON a, PS.ToRow a, Data a) => PS.Connection -> String -> a -> IO ()
insertRow conn col a = do
  let table  = map toLower $ dataTypeName $ dataTypeOf a
      fields = constrFields $ toConstr a
  void $ PS.execute conn "insert into ? (name, age) values (?, ?) " (PS.Only (PS.Many $ (PS.Plain (B.byteString $ B.pack table)):PS.toRow a))
  void $ PS.execute conn "notify person, ?" (PS.Only $ A.toJSON a)

deriving instance Show PS.Notification

-- TODO: lock while calling passesQuery to ensure cache consistency. Is this
-- important?
query :: (Show a, PS.FromRow a) => PS.Connection -> Query a -> ([a] -> IO ()) -> IO [a]
query conn q cb = do
  cq <- fillCaches conn (labelQuery q)
  rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql cq)
  rr <- newIORef rs

  PS.execute_ conn "listen person"

  forkIO $ forever $ do
    nt <- PS.getNotification conn
    traceIO $ "NOT: " ++ show nt
    case A.decode (BL.fromStrict $ PS.notificationData nt) of
      Just a -> do
        -- traceIO "DECODED"
        -- traceIO $ show a
        (sf, pq) <- passesQuery conn cq (DBValue (B.unpack $ PS.notificationChannel nt) a)
        case sf of
          Unsorted -> modifyIORef rr (++ (map snd pq))
          SortBy f -> forM_ pq $ \(_, r) -> modifyIORef rr (\rs -> snd $ insertBy' (comparing (foldExpr f)) r rs 0)
        readIORef rr >>= cb
        -- traceIO $ show pq
      Nothing -> do
        return ()
  return rs

test :: IO ()
test = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"

  rs <- query conn simplejoin (traceIO . show)
  -- traceIO $ show rs

  let rec = (Person "john" 111)

  insertRow conn "person" rec

  return ()

--------------------------------------------------------------------------------
