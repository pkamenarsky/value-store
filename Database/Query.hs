{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Database.Query where

import Control.Monad hiding (join)
import Control.Monad.Trans.State.Strict hiding (join)
import Control.Concurrent
import Control.Concurrent.MVar

import qualified Data.Aeson as A

import Data.Char
import Data.Function              (on)
import Data.IORef
import Data.List                  (intersperse, deleteBy, insertBy, find)
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
import qualified Database.PostgreSQL.Simple.Internal as PS
import qualified Database.PostgreSQL.Simple.Types as PS
import qualified Database.PostgreSQL.Simple.FromRow as PS
import qualified Database.PostgreSQL.Simple.FromField as PS
import qualified Database.PostgreSQL.Simple.ToField as PS
import qualified Database.PostgreSQL.Simple.ToRow as PS
import qualified Database.PostgreSQL.Simple.Notification as PS
import Database.PostgreSQL.Simple.Types ((:.)(..))

import System.IO.Unsafe

import GHC.Generics
import Database.Generic

import Debug.Trace

insertBy' :: (a -> a -> Ordering) -> a -> [a] -> Int -> (Int, [a])
insertBy' _   x [] i = (i, [x])
insertBy' cmp x ys@(y:ys') i
 = case cmp x y of
     EQ -> (i, x : ys')
     GT -> let (i', ys'') = insertBy' cmp x ys' (i + 1) in (i', y : ys'')
     _  -> (i, x : ys)

--------------------------------------------------------------------------------

-- NOTE: if we need to restrict the type of certain subexpressions, add a
-- phantom type, i.e.
-- data Expr tp r a where
--   Fld  :: String -> (r -> a) -> Expr Field r a

-- data KP = KP String | SP KP KP | WP
data KP t where
  KP :: String -> KP Key
  WP :: KP t
  SP :: KP t -> KP u -> KP (t :. u)

-- deriving instance Generic (KP t)
deriving instance Typeable (KP t)
deriving instance Show (KP t)
deriving instance Eq (KP t)

data K t a = K { key :: KP t, unK :: a } deriving (Eq, Generic, Typeable, Show)

cmpKP :: KP t -> KP t -> Bool
KP k   `cmpKP` KP k'    = k == k'
_      `cmpKP` WP       = True
WP     `cmpKP` _        = True
SP k l `cmpKP` SP k' l' = k `cmpKP` k' && l `cmpKP` l'
_      `cmpKP` _        = error "Keys not structurally equivalent"
-- KP _   `cmpKP` SP _ _   = error "Key not structurally equivalent"
-- SP _ _ `cmpKP` KP _     = error "Key not structurally equivalent"

{-
instance Fields a => PS.ToRow (K t a) where
  toRow a = PS.Escape (B.pack k):PS.toRow v
    where K (KP k) v = a
-}

instance Fields a => PS.FromRow (K Key a) where
  fromRow = do
    k <- PS.field
    a <- fromMaybe (error "Can't parse") <$> evalStateT cnstS ""
    -- rmn <- PS.numFieldsRemaining
    -- replicateM_ rmn (PS.field :: PS.RowParser PS.Null)
    return $ K (KP k) a

instance (PS.FromRow (K t a), PS.FromRow (K u b)) => PS.FromRow (K (t :. u) (a :. b)) where
  fromRow = do
    a <- PS.fromRow
    b <- PS.fromRow
    return $ K (SP (key a) (key b)) (unK a :. unK b)

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
  All    :: (PS.FromRow (K Key a), A.FromJSON a) => l -> Row -> Query' (K Key a) l
  Filter :: PS.FromRow (K t a) => l -> Expr a Bool -> Query' (K t a) l -> Query' (K t a) l
  Sort   :: (PS.FromRow (K t a), Ord b, Show a) => l -> Cache () (K t a) -> Expr a b -> Maybe Int -> Maybe Int -> Query' (K t a) l -> Query' (K t a) l
  Join   :: (Show a, Show b, PS.FromRow (K t a), PS.FromRow (K u b), PS.FromRow (K (t :. u) (a :. b))) => l -> Expr (a :. b) Bool -> Query' (K t a) l -> Query' (K u b) l -> Query' (K (t :. u) (a :. b)) l

deriving instance (Show l, Show a) => Show (Query' a l)

type Query a = Query' a ()
type LQuery a = Query' a String
type CQuery a = Query' a String

all :: forall a. (Typeable a, PS.FromRow (K Key a), Fields a, A.FromJSON a) => Query (K Key a)
all = All () (Row table kvs)
  where
    kvs    = "key":(map fst $ flattenObject "" $ fields (Nothing :: Maybe a))
    table  = map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)

filter :: PS.FromRow (K t a) => Expr a Bool -> Query (K t a) -> Query (K t a)
filter = Filter ()

sort :: (Ord b, Show a, PS.FromRow (K t a)) => Expr a b -> Maybe Int -> Maybe Int -> Query (K t a) -> Query (K t a)
sort = Sort () []

join :: (Show a, Show b, PS.FromRow (K t a), PS.FromRow (K u b), PS.FromRow (K (t :. u) (a :. b))) => Expr (a :. b) Bool -> Query (K t a) -> Query (K u b) -> Query (K (t :. u) (a :. b))
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

--------------------------------------------------------------------------------

data Person = Person { _name :: String, _age :: Int }
            | Robot { _ai :: Bool }
            | Undead { _kills :: Int } deriving (Eq, Generic, Typeable, Show)

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
nameE = Fld "name" $ \p -> case p of
  p@Person{..} -> Just _name
  _ -> Nothing

ageE :: Expr (Person) Int
ageE = Fld "age" $ \p -> case p of
  p@Person{..} -> Just _age
  _ -> Nothing

aiE :: Expr (Person) Bool
aiE = Fld "ai" $ \p -> case p of
  p@Robot{..} -> Just _ai
  _ -> Nothing

personE :: Expr (Address) Person
personE = Fld "person" (Just . _person)

streetE :: Expr (Address) String
streetE = Fld "street" (Just . _street)

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
q2 = sort (Fst (Fst ageE)) Nothing (Just 100) $ join ((Fst (Fst ageE) `Eqs` Fst (Snd ageE)) `And` (Fst (Fst ageE) `Eqs` Cnst 222)) (join (Fst ageE `Eqs` Snd ageE) allPersons allPersons) (join (Fst (Fst ageE) `Eqs` Snd ageE) (join (Fst ageE `Eqs` Snd ageE) allPersons allPersons) allPersons)

-- q2sql = fst $ foldQuerySql (labelQuery q2)

allPersons :: Query (K Key Person)
allPersons = all

simplejoin = {- sort (Fst ageE) Nothing (Just 100) $ -} join (Fst ageE `Eqs` Snd ageE) allPersons allPersons
simplejoinai = {- sort (Fst ageE) Nothing (Just 100) $ -} join (Fst aiE `Eqs` Snd aiE) allPersons allPersons
simplejoinsql = fst $ foldQuerySql (labelQuery simplejoin)

-- simplejoinsbstsql = fst $ foldQuerySql $ labelQuery $ filter (substFst (Fst ageE `Grt` Snd ageE) (Person "name" 666)) allPersons

simple = filter (ageE `Grt` Cnst 7) $ filter (ageE `Grt` Cnst 7) $ {- join (Fst ageE `Grt` Snd ageE) allPersons -} (filter (ageE `Grt` Cnst 6) allPersons)
simplesql = fst $ foldQuerySql (labelQuery simple)

data SortOrder a = forall b. Ord b => SortBy (Expr a b) | Unsorted

deriving instance Show (SortOrder a)

data Action = Insert | Delete deriving (Eq, Show, Generic)

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
  | r == r', A.Success (k, a) <- A.fromJSON value = return (qq, Unsorted, [(action, K (KP k) a)])
  -- FIXME: parsing
  | r == r', action == Delete, A.Success k <- A.fromJSON value = return (qq, Unsorted, [(action, K (KP k) undefined)])
  | otherwise = return (qq, Unsorted, [])
passesQuery conn row qq@(Filter l f q) = do
  (qc, so, as) <- passesQuery conn row q
  return (Filter l f qc, so, [ v | v@(action, a) <- as, Just True <- [foldExpr f (unK a)] ])
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
    go expr cache ((Delete, a):as)
      | Just _ <- find ((== key a) . key) cache = do
          as' <- PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ (Sort l cache expr (Just $ max 0 $ fromMaybe 0 offset + length cache - 1) limit q)
          (cache', as'') <- go expr (deleteBy (cmpKP `on` key) a cache) (map (Insert,) as' ++ as) -- add inserts as a result of gap after delete action
          return (cache', (Delete, a):as'') -- keep delete action in results after recursion (which adds the additional inserts)
      | otherwise = do
          (cache', as'') <- go expr cache as
          return (cache', (Delete, a):as'')
passesQuery conn row ((Join l f (ql :: Query' (K t a) String) (qr :: Query' (K u b) String)) :: Query' (K tu ab) String) = do
  (qcl, _, rl) <- passesQuery conn row ql
  (qcr, _, rr) <- passesQuery conn row qr

  if not (null rl)
    then do
      rl' <- forM rl $ \(action, r) -> do
        case action of
          Insert -> do
            ls <- case substFst f (unK r) of
              Just subst -> PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ filter subst $ fmap (const ()) qr :: IO [K u b]
              _          -> return []
            -- print $ fst $ foldQuerySql $ labelQuery $ filter (substFst f r) qr
            return [ (Insert, K (SP (key r) (key l)) (unK r :. unK l)) | l <- ls ]
          Delete -> do
            return [ (Delete, K (SP (key r) WP) (error "Deleted element")) ]
      return (Join l f qcl qcr, Unsorted, concat rl')
    else do
      rr' <- forM rr $ \(action, r) -> do
        case action of
          Insert -> do
            ls <- case substSnd f (unK r) of
              Just subst -> PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ filter subst $ fmap (const ()) ql :: IO [K t a]
              _          -> return []
            -- print $ fst $ foldQuerySql $ labelQuery $ filter (substSnd f r) ql
            return [ (Insert, K (SP (key l) (key r)) (unK l :. unK r)) | l <- ls ]
          Delete -> do
            return [ (Delete, K (SP WP (key r)) (error "Deleted element")) ]
      return (Join l f qcl qcr, Unsorted, concat rr')

reconcile' :: SortOrder a -> (Action, K t a) -> [K t a] -> [K t a]
reconcile' Unsorted (Insert, a) as      = a:as
reconcile' (SortBy expr) (Insert, a) as = insertBy (comparing (foldExpr expr . unK)) a as
reconcile' _ (Delete, a) as             = deleteBy (cmpKP `on` key) a as

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
insertRow conn k a = do
  let kvs    = "key":(map fst $ flattenObject "" $ fields (Just a))
      table  = map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)
      stmt   = "insert into "
            <> table
            <> " (" <> mconcat (intersperse ", " kvs) <> ")"
            <> " values (" <> mconcat (intersperse ", " [ "?" | _ <- kvs ]) <> ") on conflict update"

  -- traceIO stmt
  void $ PS.execute conn (PS.Query $ B.pack stmt) (PS.Only k :. a)
  void $ PS.execute conn (PS.Query $ B.pack ("notify " ++ table ++ ", ?")) (PS.Only $ A.toJSON (Insert, (k, a)))

deleteRow :: forall a. (Typeable a) => PS.Connection -> String -> Proxy a -> IO ()
deleteRow conn k _ = do
  let table  = map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)
      stmt   = "delete from " <> table <> " where key = ? "

  -- traceIO stmt
  void $ PS.execute conn (PS.Query $ B.pack stmt) (PS.Only k)
  void $ PS.execute conn (PS.Query $ B.pack ("notify " ++ table ++ ", ?")) (PS.Only $ A.toJSON (Delete, k))

deriving instance Show PS.Notification

query_ :: (Show a, PS.FromRow (K t a)) => PS.Connection -> Query (K t a) -> IO [K t a]
query_ conn q = do
  cq <- fillCaches conn (labelQuery q)
  PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql cq)

query :: (Show a, PS.FromRow (K t a)) => PS.Connection -> Query (K t a) -> ([K t a] -> IO ()) -> IO ([K t a], ThreadId)
query conn q cb = do
  cq <- fillCaches conn (labelQuery q)
  rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql cq)

  PS.execute_ conn "listen person"

  tid <- forkIO $ go cq rs
  return (rs, tid)

  where
    go q rs = do
      nt <- PS.getNotification conn
      case A.decode (BL.fromStrict $ PS.notificationData nt) of
        Just (action, a) -> do
          -- traceIO $ show action
          (q', so, as) <- passesQuery conn (DBValue action (B.unpack $ PS.notificationChannel nt) a) q
          -- traceIO "ACTIONS: "
          -- traceIO $ show as
          let rs' = reconcile so as rs
          cb rs'
          go q' rs'
        Nothing -> go q rs

data W a = W a deriving Show

instance Fields a => PS.FromRow (W a) where
  fromRow = do
    a <- fromMaybe (error "Can't parse") <$> evalStateT cnstS ""
    {-
    a <- fromMaybe (error "Can't parse K") <$> cnstM $ fields (Nothing :: Maybe a)
    rmn <- PS.numFieldsRemaining
    replicateM_ rmn (PS.field :: PS.RowParser PS.Null)
    -}
    return (W a)

test :: IO ()
test = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"

  -- rs <- PS.query_ conn "select cnst as a0_cnst, name as a0_name, age as a0_age, ai as a0_ai, kills as a0_kills from person" :: IO [W Person]
  -- traceIO $ show rs

  -- rs <- query conn (join (Fst aiE `Eqs` Snd (personE :+: aiE)) all (filter ((personE :+: aiE) `Eqs` Cnst True) all)) (traceIO . show)
  rs <- query conn simplejoinai (traceIO . show)
  -- rs <- query conn q2 (traceIO . show)
  -- rs <- query conn allPersons (traceIO . ("CB: "++ ) . show)
  traceIO $ show rs

  {-
  let rec  = (Person "john" 222)
      recr = Robot True

  insertRow conn "key3" recr

  let rec2 = (Address "doom" recr)

  insertRow conn "key2" rec2
  -}

  return ()

env :: IO (PS.Connection, Person, Address)
env = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"
  let p = Robot True
      a = Address "doom" p

  return (conn, p, a)

testSort :: IO ()
testSort = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"

  forM_ [0..50] $ \limit -> do
    PS.execute_ conn "delete from person"

    lock <- newMVar ()

    let q  = sort ageE (Just 0) (Just limit) allPersons
        cb rs = do
          rs' <- query_ conn q
          takeMVar lock
          if (rs /= rs')
            then error $ "Different results, expected: " ++ show rs' ++ ", received: " ++ show rs ++ ", query: " ++ show q
            else traceIO $ "Good, limit: " ++ show limit ++ ", size: " ++ show (length rs)
    (_, tid) <- query conn q cb

    forM [0..100] $ \k -> do
      insertRow conn ("key" ++ show k) (Person "john" k)
      putMVar lock ()

    -- FIXME: insert, delete semantics need to mirror Map
    forM [0..100] $ \k -> do
      insertRow conn ("key" ++ show k) (Person "john" k)
      putMVar lock ()
      deleteRow conn ("key" ++ show k) (Proxy :: Proxy Person)
      putMVar lock ()
      -- deleteRow conn ("key" ++ show k) (Proxy :: Proxy Person)
      -- putMVar lock ()

    killThread tid

--------------------------------------------------------------------------------
