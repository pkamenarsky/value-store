{-# LANGUAGE Arrows #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
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
{-# LANGUAGE UndecidableInstances #-}

module Database.Query where

import qualified Control.Auto as Auto

import Control.Arrow
import Control.Arrow.Operations
import Control.Arrow.Transformer as AT
import Control.Arrow.Transformer.Automaton
import Control.Arrow.Transformer.State as AST

import Control.Monad hiding (join)
import Control.Monad as MND
import Control.Monad.Trans.State.Strict as ST
import qualified Control.Monad.Trans as MT
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
import qualified Data.Map                   as M
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

import qualified Database.IxMap as Ix
import Database.Expr
import Database.Generic

import Debug.Trace

data Row = Row String [String] deriving Show

data DBValue = DBValue Action String A.Value

data Action = Insert | Delete deriving (Eq, Show, Generic)

instance A.FromJSON Action
instance A.ToJSON Action

data Key a where
  Key     :: String -> Key a
  KeyStar :: Key a
  KeyComp :: Key a -> Key b -> Key (a :. b)

deriving instance Ord (Key t)
deriving instance Show (Key t)

instance Eq (Key a) where
  Key k1        == Key k2        = k1 == k2
  _             == KeyStar       = True
  KeyStar       == _             = True
  KeyComp k1 l1 == KeyComp k2 l2 = k1 == k2 && l1 == l2
  _             == _             = False

instance Fields a => PS.FromRow (Key a, a) where
  fromRow = do
    k <- PS.field
    a <- fromMaybe (error "Can't parse") <$> evalStateT cnstS ""
    return (Key k, a)

instance (PS.FromRow (Key a, a), PS.FromRow (Key b, b)) => PS.FromRow (Key (a :. b), (a :. b)) where
  fromRow = do
    (k, a) <- PS.fromRow
    (l, b) <- PS.fromRow
    return (KeyComp k l, (a :. b))

instance {-# OVERLAPPABLE #-} Fields a => PS.ToRow a where
  toRow v = map snd $ flattenObject "" $ fields (Just v)

instance {-# OVERLAPPABLE #-} Fields a => PS.FromRow a where
  fromRow = do
    a <- fromMaybe (error "Can't parse") <$> evalStateT cnstS ""
    return a

type FR a = PS.FromRow (Key a, a)

data Query' a l where
  All    :: (FR a, A.FromJSON a)
              => l -> Row -> Query' (Key a, a) l
  Filter :: (FR a)
              => l -> Expr a Bool -> Query' (Key a, a) l -> Query' (Key a, a) l
  Sort   :: (FR a, Ord b, Show a)
              => l -> Expr a b -> Maybe Int -> Maybe Int -> Query' (Key a, a) l -> Query' (Key a, a) l
  Join   :: (Show a, Show b, FR a, FR b, FR (a :. b))
              => l -> Expr (a :. b) Bool -> Query' (Key a, a) l -> Query' (Key b, b) l -> Query' (Key (a :. b), (a :. b)) l

deriving instance (Show l, Show a) => Show (Query' a l)

deriving instance Functor (Query' a)
deriving instance Foldable (Query' a)
deriving instance Traversable (Query' a)

type Query a  = Query' a ()
type QueryL a = Query' a String

{-
all :: forall a. (Typeable a, PS.FromRow (K (Key a) a), Fields a, A.FromJSON a) => Query (K (Key a) a)
all = All () (Row table' kvs)
  where
    kvs    = "key":(map fst $ flattenObject "" $ fields (Nothing :: Maybe a))
    table  = map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)
    table' = L.filter (/= '\'') table

filter :: PS.FromRow (K t a) => Expr a Bool -> Query (K t a) -> Query (K t a)
filter = Filter ()

sort :: (Ord b, Show a, PS.FromRow (K t a)) => Expr a b -> Maybe Int -> Maybe Int -> Query (K t a) -> Query (K t a)
sort expr = Sort () (Ix.empty (comparing (foldExpr expr))) expr

join :: (Show a, Show b, PS.FromRow (K t a), PS.FromRow (K u b), PS.FromRow (K (t :. u) (a :. b))) => Expr (a :. b) Bool -> Query (K t a) -> Query (K u b) -> Query (K (t :. u) (a :. b))
join = Join ()
-}

queryLabel :: Query' a l -> l
queryLabel (All l _)        = l
queryLabel (Filter l _ _)   = l
queryLabel (Sort l _ _ _ _) = l
queryLabel (Join l _ _ _)   = l

data SortOrder a = forall b. Ord b => SortBy (Expr a b) | Unsorted

deriving instance Show (SortOrder a)

sortOrder :: Query' (t, a) l -> SortOrder a
sortOrder (All _ _)        = Unsorted
sortOrder (Filter _ _ q)   = sortOrder q
sortOrder (Sort _ e _ _ _) = SortBy e
sortOrder (Join _ _ _ _)   = Unsorted

labelQuery :: Query' a l -> QueryL a
labelQuery expr = evalState (traverse (const genVar) expr) 0

aliasColumns :: String -> Ctx -> String
aliasColumns alias ctx = concat $ intersperse ", "
  [ case calias of
      Just calias' -> calias' ++ "_" ++ col ++ " as " ++ alias ++ "_" ++ calias' ++ "_" ++ col
      Nothing      -> col ++ " as " ++ alias ++ "_" ++ col
  | (_, calias, col) <- ctx
  ]

foldQuerySql :: QueryL a -> (String, Ctx)
foldQuerySql (All l (Row row cols)) =
  ( "select " ++ aliasColumns l ([ ([], Nothing, col) | col <- cols ]) ++ " from " ++ row
  , [ ([], Just l, col) | col <- cols ]
  )
foldQuerySql (Filter l f q) =
  ( "select " ++ aliasColumns l ctx ++ " from (" ++ q' ++ ") " ++ queryLabel q ++ " where " ++ foldExprSql ctx f
  , [ (p, Just $ maybe l (\a -> l ++ "_" ++ a) a, v) | (p, a, v) <- ctx ]
  )
  where (q', ctx) = foldQuerySql q
foldQuerySql (Sort l f offset limit q) =
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

-- Operational -----------------------------------------------------------------

type Node a = PS.Connection -> DBValue -> IO [(Action, (Key a, a))]

withLocalState :: st -> (a -> b -> StateT st IO c) -> IO (a -> b -> IO c)
withLocalState st f = do
  stref <- newIORef st

  return $ \a b -> do
    st' <- readIORef stref
    (b, st'') <- runStateT (f a b) st'
    writeIORef stref st''
    return b

queryToNode :: PS.Connection -> QueryL (Key a, a) -> IO (Node a)
queryToNode conn (All _ (Row r' _)) = return $ \_ (DBValue action r value) -> do
  return [(action, (undefined, undefined))]

queryToNode conn qq@(Sort _ e offset limit q) = do
  node <- queryToNode conn q

  cache <- case limit of
    Just limit -> do
      rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql qq)
      return $ Ix.limit limit $ Ix.fromList rs (comparing (foldExpr e))
    Nothing    -> return $ Ix.empty (comparing (foldExpr e))

  withLocalState cache $ \conn dbvalue -> do
    MT.lift (node conn dbvalue) >>= go
    where
      insert v@(k, a) cache
        | cache' <- Ix.insert k a cache
        , Just i <- Ix.elemIndex k cache' = ([(Insert, v)], cache')
        | otherwise                       = ([], cache)

      go [] = return []
      go ((Insert, a):as) = do
        a'  <- ST.state (insert a)
        as' <- go as
        return $ a' ++ as'

--------------------------------------------------------------------------------

type NodeA a = Auto.Auto IO DBValue [(Action, (Key a, a))]

testNodeA :: NodeA String
testNodeA = proc dbv -> do
  r <- testNodeA2 -< dbv
  old <- cache -< do
    MT.liftIO $ putStrLn "asd"
    ST.modify $ Ix.insert (Key "2") "2"
  -- Auto.arrM print -< old
  returnA -< [(Insert, (Key "asd", "asd"))]
  where
    cache = flip Auto.mkStateM_ (Ix.empty compare) runStateT

testNodeA2 :: NodeA String
testNodeA2 = proc dbv -> do
  -- modifyA -< Ix.insert (Key "3") "3"
  -- liftIO print -< "777"
  returnA -< []

modifyA :: ArrowState s a => a (s -> s) s
modifyA = proc f -> do
  st <- fetch -< ()
  store -< f st
  fetch -< ()

runStep :: Automaton a b c -> a b (c, Automaton a b c)
runStep (Automaton f) = f

-- runTestNode :: _
runTestNodeA = Auto.stepAuto testNodeA undefined

-- queryToNodeA :: Query' (Key a, a) l -> NodeA a
-- queryToNodeA (All _ (Row r' _)) = proc (DBValue action r value) -> do
--   returnA -< [(action, (undefined, undefined))]
-- queryToNodeA (Filter _ f q) = proc dbvalue -> do
--   ts <- node -< dbvalue
--   a <- fetch -< ()
--   store -< a
--   -- r <- AT.lift (AT.lift prA) -< ()
--   returnA -< ts
--   where node = queryToNodeA q


-- NOTE: we need to ensure consistency. If something changes in the DB after
-- a notification has been received, the data has to remain consitent. I.e:
-- a delete happens, Join (or something else) expects data to be there.
{-
passesQuery :: PS.Connection
            -> DBValue
            -> CQuery (K t a)
            -> IO (CQuery (K t a), SortOrder a, [(Action, K t a)])
passesQuery conn row@(DBValue action r value) qq@(All _ (Row r' _))
  | r == r', A.Success (k, a) <- A.fromJSON value = return (qq, Unsorted, [(action, K (Key k) a)])
  -- FIXME: parsing
  | r == r', action == Delete, A.Success k <- A.fromJSON value = return (qq, Unsorted, [(action, K (Key k) undefined)])
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
      | cache' <- Ix.insert (key a) (unK a) cache
      , Just i' <- Ix.elemIndex (key a) cache'
      , i' < fromMaybe maxBound limit = do
          (cache'', as') <- go expr (Ix.take (fromMaybe maxBound limit) cache') as
          return (cache'', (Insert, a):as')
      | otherwise = go expr cache as
    go expr cache ((Delete, a):as)
      | Just _ <- Ix.lookup (key a) cache = do
          as' <- PS.query_ conn $ PS.Query $ B.pack $ fst $ foldQuerySql $ labelQuery $ (Sort l cache expr (Just $ max 0 $ fromMaybe 0 offset + Ix.size cache - 1) limit q)
          (cache', as'') <- go expr (Ix.delete (key a) cache) (map (Insert,) as' ++ as) -- add inserts as a result of gap after delete action
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
reconcile' Unsorted (Insert, a) as      = undefined -- snd $ insertByKey (\_ _ -> LT) key a as
reconcile' (SortBy expr) (Insert, a) as = undefined -- snd $ insertByKey (comparing (foldExpr expr . unK)) key a as
reconcile' _ (Delete, a) as             = undefined -- deleteAllBy (cmpKey (key a) . key) as

reconcile :: SortOrder a -> [(Action, K t a)] -> [K t a] -> [K t a]
reconcile so = flip $ foldr (reconcile' so)

fillCaches :: PS.Connection -> QueryL a -> IO (QueryL a)
fillCaches _ (All l a) = return (All l a)
fillCaches conn (Filter l a q) = do
  q' <- fillCaches conn q
  return (Filter l a q')
fillCaches conn qq@(Sort l _ expr offset limit q) = do
  cache <- case limit of
    Just _  -> do
      rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql qq)
      return $ Ix.fromList (map (\a -> (key a, unK a)) rs) (comparing (foldExpr expr))
    Nothing -> return $ Ix.empty (comparing (foldExpr expr))
  q' <- fillCaches conn q
  return (Sort l cache expr offset limit q')
fillCaches conn (Join l a ql qr) = do
  ql' <- fillCaches conn ql
  qr' <- fillCaches conn qr
  return (Join l a ql' qr')

deriving instance Show PS.Notification

query__ :: (Show a, PS.FromRow (Key t, a)) => PS.Connection -> Query (K t a) -> IO [(Key t, a)]
query__ conn q = do
  cq <- fillCaches conn (labelQuery q)
  PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql cq)

query_ :: (Show a, PS.FromRow (K t a)) => PS.Connection -> Query (K t a) -> IO [K t a]
query_ conn q = do
  cq <- fillCaches conn (labelQuery q)
  PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql cq)

query :: (Show a, PS.FromRow (K t a)) => PS.Connection -> Query (K t a) -> ([K t a] -> IO ()) -> IO ([K t a], ThreadId)
query conn q cb = do
  cq <- fillCaches conn (labelQuery q)
  rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql cq)

  -- FIXME: here we may lose data

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
-}

