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

import Control.Monad hiding (join)
import Control.Monad as MND
import Control.Monad.Trans.State.Strict as ST
import Control.Exception
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
import Data.Tuple                 (swap)
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

data DBAction = DBInsert String String A.Value | DBDelete String String deriving (Generic)

instance A.FromJSON DBAction
instance A.ToJSON DBAction

deriving instance Show PS.Notification

data Key a where
  Key     :: String -> Key a
  KeyStar :: Key a
  KeyComp :: Key a -> Key b -> Key (a :. b)

instance Show (Key a) where
  show (Key k)         = k
  show KeyStar         = "⊙"
  show (KeyComp k1 k2) = "[ " ++ show k1 ++ " ⋈ " ++ show k2 ++ " ]"

deriving instance Ord (Key t)

instance Eq (Key a) where
  Key k1        == Key k2        = k1 == k2
  _             == KeyStar       = True
  KeyStar       == _             = True
  KeyComp k1 l1 == KeyComp k2 l2 = k1 == k2 && l1 == l2
  _             == _             = False

instance {-# OVERLAPPING #-} Fields a => PS.FromRow (Key a, a) where
  fromRow = do
    k <- PS.field
    a <- fromMaybe (error "Can't parse") <$> evalStateT cnstS ""
    return (Key k, a)

instance {-# OVERLAPPING #-} (PS.FromRow (Key a, a), PS.FromRow (Key b, b)) => PS.FromRow (Key (a :. b), (a :. b)) where
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
  -- Set    :: (Show a) => Row -> [(Key a, a)] -> Query' (Key a, a) l
  All    :: (FR a, Show a, A.FromJSON a)
              => l -> Row -> Query' (Key a, a) l
  Filter :: (FR a, Show a)
              => l -> Expr a Bool -> Query' (Key a, a) l -> Query' (Key a, a) l
  Sort   :: (FR a, Ord b, Show a)
              => l -> Expr a b -> Maybe Int -> Maybe Int -> Query' (Key a, a) l -> Query' (Key a, a) l
  Join   :: (Show a, Show b, FR a, FR b, FR (a :. b))
              => l -> Expr (a :. b) Bool -> Query' (Key a, a) l -> Query' (Key b, b) l -> Query' (Key (a :. b), (a :. b)) l

instance (Show l, Show a) => Show (Query' a l) where
  show (All _ (Row row _))       = row
  show (Filter _ e q)            = "[ " ++ show e ++ " | " ++ show q ++ " ]"
  show (Sort _ e offset limit q) = "[ " ++ show e ++ " ∎ " ++ maybe "" show offset ++ " ∎ " ++ maybe "" show limit ++ " ⊨ " ++ show q ++ " ]"
  show (Join _ e ql qr)          = "[ " ++ show e ++ " | " ++ show ql ++ " ⨝ " ++ show qr ++ " ]"

deriving instance Functor (Query' a)
deriving instance Foldable (Query' a)
deriving instance Traversable (Query' a)

type Query a  = Query' a ()
type QueryL a = Query' a String

all :: forall a. (Typeable a, Show a, PS.FromRow (Key a, a), Fields a, A.FromJSON a) => Query (Key a, a)
all = All () (Row table' kvs)
  where
    kvs    = "key":(map fst $ flattenObject "" $ fields (Nothing :: Maybe a))
    table  = map toLower $ tyConName $ typeRepTyCon $ typeRep (Proxy :: Proxy a)
    table' = L.filter (/= '\'') table

{-
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

-- Labeling, folding -----------------------------------------------------------

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

data Action a = Insert (Key a, a) | Delete (Key a) deriving (Eq)

instance Show a => Show (Action a) where
  show (Insert (k, a)) = "[ ⊕ " ++ show k ++ ", " ++ show a ++ " ]"
  show (Delete k)      = "[ ⊖ " ++ show k ++ " ]"

type Node a = Auto.Auto IO DBAction [Action a]

queryToNode :: PS.Connection -> QueryL (Key a, a) -> IO (Node a)
queryToNode conn (All _ (Row row' _)) = return $ proc dbaction -> do
  case dbaction of
    DBInsert row k value
      | row == row'
      , A.Success v <- A.fromJSON value -> returnA -< [Insert (Key k, v)]
    DBDelete row k
      | row == row' -> returnA -< [Delete (Key k)]
    otherwise -> returnA -< []

queryToNode conn (Filter _ e q) = do
  node <- queryToNode conn q

  return $ proc dbaction -> do
    rs <- node -< dbaction
    returnA -<
      [ r | r <- rs
      , case r of
          Insert (_, v) -> foldExpr e v == Just True
          Delete _      -> True   -- always propagate Deletes (do we need to?)
      ]

queryToNode conn qq@(Sort l e offset limit q) = do
  node <- queryToNode conn q

  cache <- case limit of
    Just limit -> do
      rs <- query_ conn qq
      return $ Ix.fromList (comparing (foldExpr e)) limit rs
    Nothing    -> return $ Ix.empty (comparing (foldExpr e))

  putStrLn $ "  Filling cache: " ++ show cache

  -- this arrow contains a local cache; it takes a StateT computation operating
  -- on the encapsulated cache state and returns its result
  let cacheA = flip Auto.mkStateM_ cache runStateT

  return $ proc dbaction -> do
    rs <- node -< dbaction
    cacheA -< go rs

  where
    -- FIXME: when new key is inserted and element pushes back last, element remove
    -- analogously for Delete; also check offset
    insert a@(k, v) cache
      | cache' <- Ix.insert k v cache
      , Just i <- Ix.elemIndex k cache'
      , Just (kl, _) <- Ix.last cache
      , Just limit'  <- limit
      , Nothing <- Ix.elemIndex k cache
      , Ix.size cache == limit' = ([Insert a, Delete kl], cache')
      | cache' <- Ix.insert k v cache
      , Just i <- Ix.elemIndex k cache' = ([Insert a], cache')
      | otherwise                       = ([], cache)

    delete k cache
      | Just _ <- Ix.lookup k cache = do
          as <- query_ conn (Sort l e (Just $ max 0 $ fromMaybe 0 offset + Ix.size cache - 1) (Just $ fromMaybe maxBound limit - Ix.size cache + 1) q)
          (as', cache') <- ST.runStateT (go $ map Insert as) (Ix.delete k cache)
          return (Delete k : as', cache')

          -- return (Delete k : map Insert as, foldr (uncurry Ix.insert) (Ix.delete k cache) as)
      | otherwise = do
          return ([Delete k], cache)  -- always propagate Deletes (do we need to?)

    go [] = return []
    go (a:as) = do
      cache <- ST.get
      MT.lift $ putStrLn $ "  Cache : " ++ show cache
      MT.lift $ putStrLn $ "  Action: " ++ show a

      as'  <- case a of
        Insert a -> ST.state $ insert a
        Delete k -> StateT   $ delete k
      as'' <- go as
      MT.lift $ putStrLn $ "  Result: " ++ show (as' ++ as'')
      cache <- ST.get
      MT.lift $ putStrLn $ "  Cache': " ++ show cache
      return $ as' ++ as''

queryToNode conn (Join _ e ql qr) = do
  nodel <- queryToNode conn ql
  noder <- queryToNode conn qr

  return $ proc dbaction -> do
    asl <- nodel -< dbaction
    asr <- noder -< dbaction

    asl' <- Auto.arrM fillbranch -< (substFst e, qr, \l r -> KeyComp l r, \l r -> l :. r, asl)
    asr' <- Auto.arrM fillbranch -< (substSnd e, ql, \r l -> KeyComp l r, \r l -> l :. r, asr)

    returnA -< concat asl' ++ concat asr'
  where
    fillbranch :: (Show b, FR b) => (a -> Maybe (Expr b Bool), QueryL (Key b, b), Key a -> Key b -> Key c, a -> b -> c, [Action a]) -> IO [[Action c]]
    fillbranch (subst, q, combkey, combvalue, actions) =
      forM actions $ \action -> do
        case action of
          Insert (k, v) -> do
            asbr <- case subst v of
              -- is relabeling necessary here?
              Just subst -> query_ conn (labelQuery $ Filter "subst" subst q)
              _          -> return []
            return [ Insert (combkey k kbr, combvalue v vbr) | (kbr, vbr) <- asbr ]
          Delete k -> do
            return [ Delete (combkey k KeyStar) ]

query_ :: (Show a, FR a) => PS.Connection -> QueryL (Key a, a) -> IO [(Key a, a)]
query_ conn q = do
  print q
  PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql q)

-- could make that into coroutine? maybe nice for Views?
query :: (Show a, FR a) => PS.Connection -> Query (Key a, a) -> ([(Key a, a)] -> IO ()) -> IO ([(Key a, a)], ThreadId)
query conn q cb = do
  let ql   = labelQuery q
      sort = sortOrder ql

  PS.execute_ conn "listen person"

  -- FIXME: here we may lose data / get doubles?

  -- withTransaction
  as   <- query_ conn ql
  node <- queryToNode conn ql

  let ix = case sort of
        SortBy e -> Ix.fromList (comparing (foldExpr e)) maxBound as
        Unsorted -> Ix.fromList (\_ _ -> EQ) maxBound as

  tid <- forkIO $ go ql node ix

  return (Ix.toList ix, tid)
  where
    sync (Insert (k, v)) ix = Ix.insert k v ix
    sync (Delete k)      ix = Ix.delete k ix

    go q node ix = do
      nt <- PS.getNotification conn
      case A.decode (BL.fromStrict $ PS.notificationData nt) of
        Just action -> do
          -- withTransaction
          (actions, node') <- Auto.stepAuto node action
          putStrLn $ "  Ix      : " ++ show ix
          putStrLn $ "  Actions : " ++ show actions
          let ix' = foldr sync ix actions
          putStrLn $ "  Ix'     : " ++ show ix'
          cb (Ix.toList ix')
          go q node' ix'
        Nothing -> go q node ix
