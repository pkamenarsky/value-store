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
{-# LANGUAGE UndecidableInstances #-}

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
import Database.Generic

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
_      `cmpKP` _        = error "Keys not structurally equivalent"

{-
instance Fields a => PS.ToRow (K t a) where
  toRow a = PS.Escape (B.pack k):PS.toRow v
    where K (KP k) v = a
-}

instance Fields a => PS.FromRow (K (Key a) a) where
  fromRow = do
    k <- PS.field
    a <- fromMaybe (error "Can't parse") <$> evalStateT cnstS ""
    return $ K (KP k) a

instance (PS.FromRow (K t a), PS.FromRow (K u b)) => PS.FromRow (K (t :. u) (a :. b)) where
  fromRow = do
    a <- PS.fromRow
    b <- PS.fromRow
    return $ K (SP (key a) (key b)) (unK a :. unK b)

instance {-# OVERLAPPABLE #-} Fields a => PS.ToRow a where
  toRow v = map snd $ flattenObject "" $ fields (Just v)

instance {-# OVERLAPPABLE #-} Fields a => PS.FromRow a where
  fromRow = do
    a <- fromMaybe (error "Can't parse") <$> evalStateT cnstS ""
    return a

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

data Row = Row String [String] deriving Show

data DBValue = DBValue Action String A.Value

newtype Key a = Key String deriving Show

data Query' a l where
  All    :: (PS.FromRow (K (Key a) a), A.FromJSON a) => l -> Row -> Query' (K (Key a) a) l
  Filter :: PS.FromRow (K t a) => l -> Expr a Bool -> Query' (K t a) l -> Query' (K t a) l
  Sort   :: (PS.FromRow (K t a), Ord b, Show a) => l -> Ix.IxMap (KP t) a -> Expr a b -> Maybe Int -> Maybe Int -> Query' (K t a) l -> Query' (K t a) l
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
sort expr = Sort () (Ix.empty (comparing (foldExpr expr))) expr

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

keyE :: Expr a String
keyE = Fld "key" (error "keyE can be used only live")

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

data SortOrder a = forall b. Ord b => SortBy (Expr a b) | Unsorted

deriving instance Show (SortOrder a)

data Action = Insert | Delete deriving (Eq, Show, Generic)

instance A.FromJSON Action
instance A.ToJSON Action

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
fillCaches conn qq@(Sort l _ expr offset limit q) = do
  cache <- case limit of
    Just _  -> do
      -- FIXME: call fillCaches first
      -- rs <- PS.query_ conn (PS.Query $ B.pack $ fst $ foldQuerySql qq)
      rs <- undefined
      return $ Ix.fromList (map (\a -> (key a, unK a)) rs) (comparing (foldExpr expr))
    Nothing -> return $ Ix.empty (comparing (foldExpr expr))
  q' <- fillCaches conn q
  return (Sort l cache expr offset limit q')
fillCaches conn (Join l a ql qr) = do
  ql' <- fillCaches conn ql
  qr' <- fillCaches conn qr
  return (Join l a ql' qr')

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

