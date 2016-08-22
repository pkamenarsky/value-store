{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Database.Query where

import Control.Monad.State hiding (join)
import Control.Concurrent

import qualified Data.Aeson as A

import Data.Char
import Data.Function              (on)
import Data.IORef
import Data.List                  (intersperse, deleteBy, insertBy)
import Data.Maybe
import Data.Monoid                ((<>), mconcat)
import Data.Ord
import Data.Typeable

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

data KP = KP String | SP KP KP | WP deriving (Generic, Typeable, Show)

data K t a = K { key :: KP, unK :: a } deriving (Generic, Typeable, Show)

instance Eq KP where
  KP k   == KP k'    = k == k'
  _      == WP       = True
  WP     == _        = True
  SP k l == SP k' l' = k == k' && k == l'
  KP _   == SP _ _   = error "Key not structurally equivalent"
  SP _ _ == KP _     = error "Key not structurally equivalent"

instance A.FromJSON KP
instance A.ToJSON KP

instance A.FromJSON a => A.FromJSON (K t a)
instance A.ToJSON a => A.ToJSON (K t a)

instance PS.ToRow a => PS.ToRow (K t a) where
  toRow = undefined

instance PS.FromRow a => PS.FromRow (K t a) where
  fromRow = undefined

data Expr r a where
  (:+:) :: Expr a b -> Expr b c -> Expr a c
  Cnst  :: Show a => a -> Expr r a
  Fld   :: String -> (r -> a) -> Expr r a
  Fst   :: Show a => Expr r a -> Expr (r :. s) a
  Snd   :: Show a => Expr s a -> Expr (r :. s) a
  And   :: Expr r Bool -> Expr r Bool -> Expr r Bool
  Grt   :: Ord a => Expr r a -> Expr r a -> Expr r Bool
  Eqs   :: Eq  a => Expr r a -> Expr r a -> Expr r Bool
  Plus  :: Num n => Expr r n -> Expr r n -> Expr r n

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
foldExprSql ctx (Fld name _ :+: Fld name' _) = lookupVar ctx (name ++ "_" ++ name')
foldExprSql ctx (_ :+: _) = "Can compose only fields"
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

data DBValue = DBValue Action String A.Value

type Key = String

data Query' a l where
  All    :: A.FromJSON a => l -> Row -> Query' (K Key a) l
  Filter :: l -> Expr a Bool -> Query' (K t a) l -> Query' (K t a) l
  Sort   :: (Ord b, PS.FromRow a, Show a) => l -> Cache () (K t a) -> Expr a b -> Maybe Int -> Maybe Int -> Query' (K t a) l -> Query' (K t a) l
  Join   :: (Show a, Show b, PS.FromRow a, PS.FromRow b) => l -> Expr (a :. b) Bool -> Query' (K t a) l -> Query' (K u b) l -> Query' (K (t :. u) (a :. b)) l

deriving instance (Show l, Show a) => Show (Query' a l)

type Query a = Query' a ()
type LQuery a = Query' a String
type CQuery a = Query' a String

all :: forall a. (Typeable a, Fields a, A.FromJSON a) => Query (K Key a)
all = All () (Row table [ k | (k, _) <- kvs ])
  where
    kvs    = flattenObject "" $ fields (Nothing :: Maybe a)
    table  = map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)

filter :: Expr a Bool -> Query (K t a) -> Query (K t a)
filter = Filter ()

sort :: (Ord b, Show a, PS.FromRow a) => Expr a b -> Maybe Int -> Maybe Int -> Query (K t a) -> Query (K t a)
sort = Sort () []

join :: (Show a, Show b, PS.FromRow a, PS.FromRow b) => Expr (a :. b) Bool -> Query (K t a) -> Query (K u b) -> Query (K (t :. u) (a :. b))
join = Join ()

queryLabel :: Query' a l -> l
queryLabel (All l _) = l
queryLabel (Filter l _ _) = l
queryLabel (Sort l _ _ _ _ _) = l
queryLabel (Join l _ _ _) = l

deriving instance Functor (Query' a)
deriving instance Foldable (Query' a)
deriving instance Traversable (Query' a)

labelQuery :: Query' a l -> LQuery a
labelQuery expr = evalState (traverse (const genVar) expr) 0

substFst :: Expr (l :. r) a -> l -> Expr r a
substFst (Cnst a) sub = Cnst a
substFst (Fld _ _) sub = error "Invalid field access"
substFst (_ :+: _ ) sub = error "Invalid field access"
substFst (Fst f) sub = Cnst (foldExpr f sub)
substFst (Snd f) sub = f
substFst (And ql qr) sub = And (substFst ql sub) (substFst qr sub)
substFst (Grt ql qr) sub = Grt (substFst ql sub) (substFst qr sub)
substFst (Eqs ql qr) sub = Eqs (substFst ql sub) (substFst qr sub)
substFst (Plus ql qr) sub = Plus (substFst ql sub) (substFst qr sub)

substSnd :: Expr (l :. r) a -> r -> Expr l a
substSnd (Cnst a) sub = Cnst a
substSnd (Fld _ _) sub = error "Invalid field access"
substSnd (_ :+: _ ) sub = error "Invalid field access"
substSnd (Fst f) sub = f
substSnd (Snd f) sub = Cnst (foldExpr f sub)
substSnd (And ql qr) sub = And (substSnd ql sub) (substSnd qr sub)
substSnd (Grt ql qr) sub = Grt (substSnd ql sub) (substSnd qr sub)
substSnd (Eqs ql qr) sub = Eqs (substSnd ql sub) (substSnd qr sub)
substSnd (Plus ql qr) sub = Plus (substSnd ql sub) (substSnd qr sub)

foldExpr :: Expr r a -> (r -> a)
foldExpr (Cnst a) = const a
foldExpr (Fld _ get) = get
foldExpr (f :+: g) = foldExpr g . foldExpr f
foldExpr (Fst f) = \(r :. _) -> foldExpr f r
foldExpr (Snd f) = \(_ :. r) -> foldExpr f r
foldExpr (And a b) = \r -> foldExpr a r && foldExpr b r
foldExpr (Grt a b) = \r -> foldExpr a r > foldExpr b r
foldExpr (Eqs a b) = \r -> foldExpr a r == foldExpr b r
foldExpr (Plus a b) = \r -> foldExpr a r + foldExpr b r

--------------------------------------------------------------------------------

data Person = Person { _name :: String, _age :: Int }
            | Robot { _ai :: Bool }
            | Undead { _kills :: Int } deriving (Generic, Typeable, Show)

data Address = Address { _street :: String, _person :: Person } deriving (Generic, Typeable, Show)

instance A.FromJSON Person
instance A.ToJSON Person

instance A.FromJSON Address
instance A.ToJSON Address

instance Fields Person
instance Fields Address

data Image = Horizontal { what :: Int } | Vertical { who :: Person, why :: String } deriving (Generic, Show)

instance Fields Image

nameE :: Expr (Person) String
nameE = Fld "name" _name

ageE :: Expr (Person) Int
ageE = Fld "age" _age

aiE :: Expr (Person) Bool
aiE = Fld "ai" _ai

personE :: Expr (Address) Person
personE = Fld "person" _person

streetE :: Expr (Address) String
streetE = Fld "street" _street

--------------------------------------------------------------------------------

{-
class Actionable k v where
  update :: Action -> k -> [K k v] -> [K k v]

data Wildcard

instance Actionable Key b where
  update _ k v = v

instance Actionable Wildcard b where
  update _ k v = []

instance (Actionable j a, Actionable k b) => Actionable (j :. k) (a :. b) where
  update action (j :. k) v = [ K k' (a :. b) | (K k' a, K k'' b) <- zip js ks ]
    where
      js = update action j [ K k' a | K k' (a :. b) <- v ]
      ks = update action k [ K k' b | K k' (a :. b) <- v ]

kvs :: [K (Key :. (Wildcard :. Key)) (Person :. (Person :. Person))]
kvs = undefined

kvs' = update Delete undefined kvs
-}

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
foldQuerySql (Sort l _ f offset limit q) =
  ( "select " ++ aliasColumns l ctx ++ " from (" ++ q' ++ ") " ++ queryLabel q ++ " order by " ++ foldExprSql ctx f  ++ maybe "" ((" limit " ++) . show) limit ++ maybe "" ((" offset " ++) . show) offset
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

ql = (filter (ageE `Grt` Cnst 3) $ sort nameE Nothing (Just 10) $ filter (ageE `Grt` Cnst 6) $ all)
qr :: Query (K Key Person)
qr = all
-- q1 :: _
q1 = {- join (Fst ageE `Grt` Snd (Fst ageE)) ql -} (join (Fst ageE `Grt` Snd ageE) ql qr)

q1sql = fst $ foldQuerySql (labelQuery q1)

-- q2 :: _ -- Query ((Person, Person), Person)
q2 = sort (Fst (Fst ageE)) Nothing (Just 100) $ join ((Fst (Fst ageE) `Grt` Fst (Snd ageE)) `And` (Fst (Fst ageE) `Grt` Cnst 666)) (join (Fst ageE `Grt` Snd ageE) allPersons allPersons) (join (Fst (Fst ageE) `Grt` Snd ageE) (join (Fst ageE `Grt` Snd ageE) allPersons allPersons) allPersons)

-- q2sql = fst $ foldQuerySql (labelQuery q2)

allPersons :: Query (K Key Person)
allPersons = all

simplejoin = sort (Fst ageE) Nothing (Just 100) $ join (Fst ageE `Eqs` Snd ageE) allPersons allPersons
simplejoinsql = fst $ foldQuerySql (labelQuery simplejoin)

-- simplejoinsbstsql = fst $ foldQuerySql $ labelQuery $ filter (substFst (Fst ageE `Grt` Snd ageE) (Person "name" 666)) allPersons

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

data Action = Insert | Delete deriving (Generic)

instance A.FromJSON Action
instance A.ToJSON Action

type Cache t a = [a]

-- NOTE: we need to ensure consistency. If something changes in the DB after
-- a notification has been received, the data has to remain consitent. I.e:
-- a delete happens, Join (or something else) expects data to be there.
passesQuery :: PS.Connection
            -> DBValue
            -> CQuery (K t a)
            -> IO (CQuery (K t a), SortOrder a, [(Action, K t a)])
passesQuery conn row@(DBValue action r value) qq@(All _ (Row r' _))
  | r == r', A.Success a <- A.fromJSON value = return (qq, Unsorted, [(action, a)])
  | otherwise = return (qq, Unsorted, [])
passesQuery conn row qq@(Filter l f q) = do
  (qc, so, as) <- passesQuery conn row q
  return (Filter l f qc, so, [ v | v@(action, a) <- as, foldExpr f (unK a) ])
passesQuery conn row (Sort l cache expr offset limit q) = do
  (qc, _, as)   <- passesQuery conn row q
  (cache', as') <- go expr cache as
  return (Sort l cache' expr offset limit qc, SortBy expr, as')
  where
    go expr cache [] = return (cache, [])
    go expr cache ((Insert, a):as)
      | (i', cache') <- insertBy' (comparing (foldExpr expr . unK)) a cache 0
      , i' < fromMaybe maxBound limit = do
          (cache'', as') <- go expr (take (fromMaybe maxBound limit) cache') as
          return (cache'', (Insert, a):as')
      | otherwise = go expr cache as
    go expr cache ((Delete, a):as) = do
      -- TODO: test sort
      as' <- PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ (Sort l cache expr (Just $ fromMaybe 0 offset + length cache - 1) limit q)
      (cache', as'') <- go expr (deleteBy ((==) `on` key) a cache) (map (Insert,) as' ++ as) -- add inserts as a result of gap after delete action
      return (cache', (Delete, a):as'') -- keep delete action in results after recursion (which adds the additional inserts)
passesQuery conn row (Join l f ql qr) = do
  (qcl, _, rl) <- passesQuery conn row ql
  (qcr, _, rr) <- passesQuery conn row qr

  if not (null rl)
    then do
      rl' <- forM rl $ \(action, r) -> do
        case action of
          Insert -> do
            ls <- PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ filter (substFst f (unK r)) $ fmap (const ()) qr
            -- print $ fst $ foldQuerySql $ labelQuery $ filter (substFst f r) qr
            return [ (Insert, K (SP (key r) (key l)) (unK r :. unK l)) | l <- ls ]
          Delete -> do
            return [ (Delete, K (SP (key r) WP) (error "Deleted element")) ]
      return (Join l f qcl qcr, Unsorted, concat rl')
    else do
      rr' <- forM rr $ \(action, r) -> do
        case action of
          Insert -> do
            ls <- PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ filter (substSnd f (unK r)) $ fmap (const ()) ql
            -- print $ fst $ foldQuerySql $ labelQuery $ filter (substSnd f r) ql
            return [ (Insert, K (SP (key l) (key r)) (unK l :. unK r)) | l <- ls ]
          Delete -> do
            return [ (Delete, K (SP WP (key r)) (error "Deleted element")) ]
      return (Join l f qcl qcr, Unsorted, concat rr')

reconcile' :: SortOrder a -> (Action, K t a) -> [K t a] -> [K t a]
reconcile' Unsorted (Insert, a) as      = a:as
reconcile' (SortBy expr) (Insert, a) as = insertBy (comparing (foldExpr expr . unK)) a as
reconcile' _ (Delete, a) as             = deleteBy ((==) `on` key) a as

reconcile :: SortOrder a -> [(Action, K t a)] -> [K t a] -> [K t a]
reconcile so = flip $ foldr (reconcile' so)

fillCaches :: PS.Connection -> LQuery a -> IO (LQuery a)
fillCaches _ (All l a) = return (All l a)
fillCaches conn (Filter l a q) = do
  q' <- fillCaches conn q
  return (Filter l a q')
fillCaches conn qq@(Sort l _ b offset limit q) = do
  cache <- case limit of
    Just _  -> do
      rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql qq)
      return rs
    Nothing -> return []
  q' <- fillCaches conn q
  return (Sort l cache b offset limit q')
fillCaches conn (Join l a ql qr) = do
  ql' <- fillCaches conn ql
  qr' <- fillCaches conn qr
  return (Join l a ql' qr')

listen :: (String -> A.Value -> IO ()) -> IO ()
listen = undefined

mkRowParser :: Fields a => PS.RowParser a
mkRowParser = undefined

insertRow :: forall a. (Typeable a, A.ToJSON a, Fields a, PS.ToRow a) => PS.Connection -> String -> a -> IO ()
insertRow conn col a = do
  let kvs    = flattenObject "" $ fields (Just a)
      table  = map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)
      stmt   = "insert into "
            <> table
            <> " (" <> mconcat (intersperse ", " [ k | (k, _) <- kvs ]) <> ")"
            <> " values (" <> mconcat (intersperse ", " [ "?" | _ <- kvs ]) <> ")"
  print stmt
  void $ PS.execute conn (PS.Query $ B.pack stmt) a
  void $ PS.execute conn (PS.Query $ B.pack ("notify " ++ table ++ ", ?")) (PS.Only $ A.toJSON a)

deriving instance Show PS.Notification

query :: (Show a, PS.FromRow a) => PS.Connection -> Query (K t a) -> ([K t a] -> IO ()) -> IO [K t a]
query conn q cb = do
  cq <- fillCaches conn (labelQuery q)
  rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql cq)

  PS.execute_ conn "listen person"

  forkIO $ go cq rs

  return rs
  where
    go q rs = do
      nt <- PS.getNotification conn
      case A.decode (BL.fromStrict $ PS.notificationData nt) of
        Just (action, a) -> do
          (q', so, as) <- passesQuery conn (DBValue action (B.unpack $ PS.notificationChannel nt) a) q
          let rs' = reconcile so as rs
          cb rs'
          go q' rs'
        Nothing -> go q rs


test :: IO ()
test = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"

  {-
  rs <- query conn (join (Fst aiE `Eqs` Snd (personE :+: aiE)) all (filter ((personE :+: aiE) `Eqs` Cnst True) all)) (traceIO . show)
  traceIO $ show rs
  -}

  let rec  = (Person "john" 222)
      recr = Robot True

  insertRow conn "person" rec

  let rec2 = (Address "doom" recr)

  insertRow conn "person" rec2

  return ()

--------------------------------------------------------------------------------
