{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Database.Query where

import Control.Monad hiding (join)
import Control.Monad.Trans.State.Strict
import Control.Concurrent
import Control.Concurrent.MVar

import qualified Data.Aeson as A

import Data.Char
import Data.Function              (on)
import Data.IORef
import Data.List                  (intersperse, find)
import qualified Data.List        as L
import Data.Maybe
import Data.Monoid                ((<>), mconcat)
import Data.Ord
import qualified Data.Set                   as S
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
import GHC.TypeLits

import Bookkeeper hiding (Key, get, modify)
import Bookkeeper.Permissions hiding (modify, read, insert)
import qualified Bookkeeper.Permissions as PRM

import Database.Generic
import Database.Bookkeeper

import qualified Data.Type.Map as Map
import qualified Data.Type.Set as Set

import Debug.Trace

deleteAllBy :: (a -> Bool) -> [a] -> [a]
deleteAllBy f [] = []
deleteAllBy f (x:xs)
  | f x = deleteAllBy f xs
  | otherwise = x:deleteAllBy f xs

insertBy' :: (a -> a -> Ordering) -> Int -> a -> [a] -> (Int, [a])
insertBy' _   i x [] = (i, [x])
insertBy' cmp i x ys@(y:ys')
 = case cmp x y of
     GT -> let (i', ys'') = insertBy' cmp (i + 1) x ys' in (i', y : ys'')
     _  -> (i, x : ys)

insertByKey :: Eq b => (a -> a -> Ordering) -> (a -> b) -> a -> [a] -> (Int, [a])
insertByKey f k x = insertBy' f 0 x . deleteAllBy ((k x ==) . k)

--------------------------------------------------------------------------------

-- NOTE: if we need to restrict the type of certain subexpressions, add a
-- phantom type, i.e.
-- data Expr tp r a where
--   Fld  :: String -> (r -> a) -> Expr Field r a

-- data KP = KP String | SP KP KP | WP
data KP t where
  KP :: String -> KP (Key a)
  WP :: KP t
  SP :: KP t -> KP u -> KP (t :. u)

-- deriving instance Generic (KP t)
deriving instance Typeable (KP t)
deriving instance Eq (KP t)
deriving instance Ord (KP t)
deriving instance Show (KP t)

data K t a = K { key :: KP t, unK :: a } deriving (Eq, Ord, Generic, Typeable, Show)

cmpKP :: KP t -> KP t -> Bool
KP k   `cmpKP` KP k'    = k == k'
_      `cmpKP` WP       = True
WP     `cmpKP` _        = True
SP k l `cmpKP` SP k' l' = k `cmpKP` k' && l `cmpKP` l'
-- _      `cmpKP` _        = error "Keys not structurally equivalent"
-- KP _   `cmpKP` SP _ _   = error "Key not structurally equivalent"
-- SP _ _ `cmpKP` KP _     = error "Key not structurally equivalent"

{-
instance Fields a => PS.ToRow (K t a) where
  toRow a = PS.Escape (B.pack k):PS.toRow v
    where K (KP k) v = a
-}

instance Fields a => PS.FromRow (K (Key a) a) where
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

class IsExpr e r n where
  toExpr :: e r n

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

instance Show (a -> Maybe b) where
  show _ = "(a -> Maybe b)"

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
-- TODO: FIXME
foldExprSql ctx (Cnst a) = "'" ++ (L.filter (/= '\"') $ show a) ++ "'"
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

newtype Key a = Key String

data Query' a l where
  All    :: (PS.FromRow (K (Key a) a), A.FromJSON a) => l -> Row -> Query' (K (Key a) a) l
  Filter :: PS.FromRow (K t a) => l -> Expr a Bool -> Query' (K t a) l -> Query' (K t a) l
  Sort   :: (PS.FromRow (K t a), Ord b, Show a) => l -> Cache () (K t a) -> Expr a b -> Maybe Int -> Maybe Int -> Query' (K t a) l -> Query' (K t a) l
  Join   :: (Show a, Show b, PS.FromRow (K t a), PS.FromRow (K u b), PS.FromRow (K (t :. u) (a :. b))) => l -> Expr (a :. b) Bool -> Query' (K t a) l -> Query' (K u b) l -> Query' (K (t :. u) (a :. b)) l

deriving instance (Show l, Show a) => Show (Query' a l)

type Query a = Query' a ()
type LQuery a = Query' a String
type CQuery a = Query' a String

all :: forall a. (Typeable a, PS.FromRow (K (Key a) a), Fields a, A.FromJSON a) => Query (K (Key a) a)
all = All () (Row table' kvs)
  where
    kvs    = "key":(map fst $ flattenObject "" $ fields (Nothing :: Maybe a))
    table  = map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)
    table' = L.filter (/= '\'') table

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

instance (A.FromJSON a) => A.FromJSON (Permission (prf :: [Map.Mapping Symbol *]) a)
instance (A.ToJSON a)   => A.ToJSON (Permission (prf :: [Map.Mapping Symbol *]) a)

instance (PS.ToField a) => PS.ToField (Permission (prf :: [Map.Mapping Symbol *]) a) where
  toField a = PS.toField (unsafeUnpackPermission a)

instance (PS.FromField a) => PS.FromField (Permission (prf :: [Map.Mapping Symbol *]) a) where
  fromField f dat = unsafePermission <$> PS.fromField f dat

data Admin = Admin

type UndeadT = Book '[ "_kills" :=> Permission '[ "read" :=> Admin ] Int ]

data Person' a = Person { _name :: String, _age :: Int }
               | Robot { _ai :: Bool }
               --  | Undead { _kills :: Int } deriving (Eq, Ord, Generic, Typeable, Show)
               | Undead a deriving (Eq, {- Ord, -} Generic, Typeable, Show)

type Person = Person' UndeadT

data Address = Address { _street :: String, _person :: Person } deriving (Generic, Typeable, Show)

instance A.FromJSON a => A.FromJSON (Person' a)
instance A.ToJSON a => A.ToJSON (Person' a)

instance A.FromJSON Address
instance A.ToJSON Address

instance Fields a => Fields (Person' a)
instance Fields Address

data Image = Horizontal { what :: Int } | Vertical { who :: Person, why :: String } deriving (Generic, Show)

instance Fields Image

keyE :: Expr a String
keyE = Fld "key" (error "keyE can be used only live")

killsE :: Expr (Person) Int
killsE = Fld "kills" $ \p -> case p of
  Undead p -> Just $ unsafeUnpackPermission $ p ?: #_kills
  _ -> Nothing

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
qr :: Query (K (Key Person) Person)
qr = all
-- q1 :: _
q1 = {- join (Fst ageE `Grt` Snd (Fst ageE)) ql -} (join (Fst ageE `Grt` Snd ageE) ql qr)

q1sql = fst $ foldQuerySql (labelQuery q1)

-- q2 :: _ -- Query ((Person, Person), Person)
q2 = sort (Fst (Fst ageE)) Nothing (Just 100) $ join ((Fst (Fst ageE) `Eqs` Fst (Snd ageE)) `And` (Fst (Fst ageE) `Eqs` Cnst 222)) (join (Fst ageE `Eqs` Snd ageE) allPersons allPersons) (join (Fst (Fst ageE) `Eqs` Snd ageE) (join (Fst ageE `Eqs` Snd ageE) allPersons allPersons) allPersons)

-- q2sql = fst $ foldQuerySql (labelQuery q2)

allPersons :: Query (K (Key Person) Person)
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
  return (Filter l f qc, so, [ v | v@(action, a) <- as
                                 , case action of
                                    Insert -> foldExpr f (unK a) == Just True
                                    Delete -> True
                             ])
passesQuery conn row (Sort l cache expr offset limit q) = do
  (qc, _, as)   <- passesQuery conn row q
  (cache', as') <- go expr cache as
  return (Sort l cache' expr offset limit qc, SortBy expr, as')
  where
    go expr cache [] = return (cache, [])
    go expr cache ((Insert, a):as)
      | (i', cache') <- insertByKey (comparing (foldExpr expr . unK)) key a cache
      , i' < fromMaybe maxBound limit = do
          (cache'', as') <- go expr (take (fromMaybe maxBound limit) cache') as
          return (cache'', (Insert, a):as')
      | otherwise = go expr cache as
    go expr cache ((Delete, a):as)
      | Just _ <- find ((== key a) . key) cache = do
          as' <- PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ (Sort l cache expr (Just $ max 0 $ fromMaybe 0 offset + length cache - 1) limit q)
          (cache', as'') <- go expr (deleteAllBy (cmpKP (key a) . key) cache) (map (Insert,) as' ++ as) -- add inserts as a result of gap after delete action
          return (cache', (Delete, a):as'') -- keep delete action in results after recursion (which adds the additional inserts)
      | otherwise = do
          (cache', as'') <- go expr cache as
          return (cache', (Delete, a):as'')
passesQuery conn row ((Join l f (ql :: Query' (K t a) String) (qr :: Query' (K u b) String)) :: Query' (K tu ab) String) = do
  (qcl, _, rl) <- passesQuery conn row ql
  (qcr, _, rr) <- passesQuery conn row qr

  rl' <- forM rl $ \(action, r) -> do
    case action of
      Insert -> do
        ls <- case substFst f (unK r) of
          Just subst -> PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ filter subst $ fmap (const ()) qr :: IO [K u b]
          _          -> return []
        -- print $ fst $ foldQuerySql $ labelQuery $ filter (substFst f r) qr
        return [ (Insert, K (SP (key r) (key l)) (unK r :. unK l)) | l <- ls ]
      Delete -> do
        traceIO $ show $ SP (key r) WP
        return [ (Delete, K (SP (key r) WP) (error "Deleted element")) ]

  rr' <- forM rr $ \(action, r) -> do
    case action of
      Insert -> do
        ls <- case substSnd f (unK r) of
          Just subst -> PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ filter subst $ fmap (const ()) ql :: IO [K t a]
          _          -> return []
        -- print $ fst $ foldQuerySql $ labelQuery $ filter (substSnd f r) ql
        return [ (Insert, K (SP (key l) (key r)) (unK l :. unK r)) | l <- ls ]
      Delete -> do
        traceIO $ show $ SP WP (key r)
        return [ (Delete, K (SP WP (key r)) (error "Deleted element")) ]

  return (Join l f qcl qcr, Unsorted, concat rl' ++ concat rr')

reconcile' :: SortOrder a -> (Action, K t a) -> [K t a] -> [K t a]
reconcile' Unsorted (Insert, a) as      = snd $ insertByKey (\_ _ -> LT) key a as
reconcile' (SortBy expr) (Insert, a) as = snd $ insertByKey (comparing (foldExpr expr . unK)) key a as
reconcile' _ (Delete, a) as             = deleteAllBy (cmpKP (key a) . key) as

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

insertRow :: forall a. (Show a, A.ToJSON a, Fields a, PS.ToRow a) => PS.Connection -> String -> a -> IO ()
insertRow conn k a = do
  let kvs    = "key":(map fst $ flattenObject "" $ fields (Just a))
      table  = "person" -- map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)
      stmt   = "insert into "
            <> table
            <> " (" <> mconcat (intersperse ", " kvs) <> ")"
            <> " values (" <> mconcat (intersperse ", " [ "?" | _ <- kvs ]) <> ")"
            <> " on conflict (key) do update set "
            <> mconcat (intersperse ", " [ k ++ " = ? " | k <- tail kvs ])

  traceIO $ "I, key: " ++ show k ++ ", value: " ++  show a

  -- traceIO stmt
  void $ PS.execute conn (PS.Query $ B.pack stmt) (PS.Only k :. a :. a)
  void $ PS.execute conn (PS.Query $ B.pack ("notify " ++ table ++ ", ?")) (PS.Only $ A.toJSON (Insert, (k, a)))

deleteRow :: forall a. (Typeable a) => PS.Connection -> String -> Proxy a -> IO ()
deleteRow conn k _ = do
  let table  = map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)
      stmt   = "delete from " <> table <> " where key = ? "

  traceIO $ "D, key: " ++ show k

  -- traceIO stmt
  void $ PS.execute conn (PS.Query $ B.pack stmt) (PS.Only k)
  void $ PS.execute conn (PS.Query $ B.pack ("notify " ++ table ++ ", ?")) (PS.Only $ A.toJSON (Delete, k))

modifyRow' :: forall a prf. (Generic a, Fields (MapADTM "modify" prf a), A.FromJSON a, A.ToJSON (MapADTM "modify" prf a), Typeable (MapADTM "modify" prf a), Show (MapADTM "modify" prf a), Generic (MapADTM "modify" prf a), MapGeneric "modify" prf (Rep a) (Rep (MapADTM "modify" prf a)), Show a, Typeable a, A.ToJSON a, Fields a, PS.FromRow a)
          => PS.Connection
          -> Set.Set prf
          -> a
          -> (MapADTM "modify" prf a -> MapADTM "modify" prf a)
          -> IO ()
modifyRow' conn prf a f = do
  let (to, from) = PRM.mapADT (Proxy :: Proxy "modify") prf
  let a' = from . f . to $ a
  print a'

modifyRow :: forall a prf.
           ( Generic a
           , Fields (MapADTM "modify" prf a)
           , A.FromJSON a
           , A.ToJSON (MapADTM "modify" prf a)
           , Typeable (MapADTM "modify" prf a)
           , Show (MapADTM "modify" prf a)
           , Generic (MapADTM "modify" prf a)
           , MapGeneric "modify" prf (Rep a) (Rep (MapADTM "modify" prf a))
           , Show a
           , Typeable a
           , A.ToJSON a
           , Fields a
           , PS.FromRow a
           , PS.ToRow a
           )
          => PS.Connection
          -> Set.Set prf
          -> Key a
          -> (MapADTM "modify" prf a -> MapADTM "modify" prf a)
          -> IO ()
modifyRow conn prf (Key key) f = do
  [a] <- query_ conn (filter (keyE `Eqs` Cnst key) $ all) :: IO [K (Key a) a]
  print a
  let (to, from) = PRM.mapADT (Proxy :: Proxy "modify") prf
  let a' = from . f . to $ unK a
  print a'
  insertRow conn key a'

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

person :: Person
person = Undead $ emptyBook & #_kills =: unsafePermission 8

person1 = case Database.Query.person of
  Undead p -> Undead (p & #_kills =: unsafePermission 7)

test :: IO ()
test = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"

  -- modifyRow' conn (Admin `Set.Ext` Set.Empty) Database.Query.person $ \(p) ->
  --   case p of
  --     Undead p -> Undead (p & #_kills =: 7)

  modifyRow conn (Admin `Set.Ext` Set.Empty) (Key "key0" :: Key Person) $ \(p) ->
    case p of
      Undead p -> Undead (p & #_kills =: 9)

  -- rs <- PS.query_ conn "select cnst as a0_cnst, name as a0_name, age as a0_age, ai as a0_ai, kills as a0_kills from person" :: IO [W Person]
  -- traceIO $ show rs

  -- rs <- query conn (join (Fst aiE `Eqs` Snd (personE :+: aiE)) all (filter ((personE :+: aiE) `Eqs` Cnst True) all)) (traceIO . show)
  -- rs <- query conn simplejoinai (traceIO . show)
  rs <- query conn (filter (killsE `Eqs` Cnst 9) $ allPersons) (traceIO . show)
  -- rs <- query conn q2 (traceIO . show)
  -- rs <- query conn allPersons (traceIO . ("CB: "++ ) . show)

  print "--- Query"

  forM_ (fst rs) $ \p -> do
    case unK p of
      Undead p -> print (PRM.read (Admin `Set.Ext` Set.Empty) p)
      _ -> return ()

  -- traceIO $ show rs

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

  insertRow conn ("key0") (Undead $ emptyBook & #_kills =: unsafePermission 5 :: Person)

  {-
  forM_ [0..10] $ \limit -> do
    PS.execute_ conn "delete from person"

    lock <- newMVar ()

    let q  -- = join (Fst ageE `Grt` Snd ageE) allPersons $ sort ageE (Just 0) (Just limit) $ filter ((ageE `Grt` Cnst 5)) allPersons
           = join (Fst ageE `Eqs` Snd ageE) allPersons $ sort ageE (Just 0) (Just limit) $ filter ((ageE `Grt` Cnst 5)) allPersons
             -- join (Fst ageE `Eqs` Snd ageE) allPersons allPersons
        cb rs = do
          rs' <- query_ conn q
          -- if (S.fromList rs /= S.fromList rs')
          if (rs /= rs')
            then do
              traceIO "Different results, expected: "
              traceIO $ show rs'
              traceIO "Received: "
              traceIO $ show rs
              traceIO "Difference: "
              -- traceIO $ show ((S.fromList rs' `S.difference` S.fromList rs) `S.union` (S.fromList rs `S.difference` S.fromList rs'))
              traceIO "Query: "
              traceIO $ show q
              error "Aborting"
            else do
              traceIO $ "Good, limit: " ++ show limit ++ ", size: " ++ show (length rs)
              takeMVar lock
    (_, tid) <- query conn q cb

    forM [0..20] $ \k -> do
      insertRow conn ("key" ++ show k) (Person "john" k)
      putMVar lock ()

    forM [0..20] $ \k -> do
      insertRow conn ("key" ++ show k) (Person "john" k)
      putMVar lock ()
      insertRow conn ("key" ++ show k) (Person "john" k)
      putMVar lock ()
      deleteRow conn ("key" ++ show k) (Proxy :: Proxy Person)
      putMVar lock ()
      deleteRow conn ("key" ++ show k) (Proxy :: Proxy Person)
      putMVar lock ()

    killThread tid
  -}

--------------------------------------------------------------------------------
