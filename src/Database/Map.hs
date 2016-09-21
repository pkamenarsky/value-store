{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Database.Map where

import qualified Data.Aeson as A
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Char8 as B

import Data.Char                  (toLower)
import Data.List                  (intersperse, find)
import Data.Monoid                ((<>), mconcat)
import Data.Typeable

import Control.Monad hiding (join)

import qualified Database.PostgreSQL.Simple as PS
import qualified Database.PostgreSQL.Simple.Types as PS
import qualified Database.PostgreSQL.Simple.ToRow as PS
import Database.PostgreSQL.Simple.Types ((:.)(..))

import qualified Bookkeeper.Permissions as PRM
import Bookkeeper.Permissions hiding (modify, read, insert)

import Database.Bookkeeper
import Database.Expr
import Database.Generic
import Database.Query

import qualified Data.Type.Set as Set

import Prelude hiding (filter, sort, all, join)

import GHC.Generics

import Debug.Trace

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
           , PS.FromRow (K (Key a) a)
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

