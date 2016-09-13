{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Database.Bookkeeper where

import Bookkeeper
import Bookkeeper.Internal

import Data.Proxy

import qualified Data.ByteString.Char8 as BC

import Database.Generic

import qualified Database.PostgreSQL.Simple.FromField as PS
import qualified Database.PostgreSQL.Simple.ToField as PS
import qualified Database.PostgreSQL.Simple.FromRow as PS
import qualified Database.PostgreSQL.Simple.ToRow as PS
import qualified Database.PostgreSQL.Simple.Internal as PS

import qualified Data.Type.Map as Map

import GHC.OverloadedLabels
import GHC.TypeLits

instance Fields (Book' '[]) where
  fields _ = Object []
  cnst = undefined
  cnstM = undefined
  cnstS = undefined

instance (KnownSymbol k, Fields v, Fields (Book' m)) => Fields (Book' (k :=> v ': m)) where
  fields (Just (Book (Map.Ext k v m))) = Object $ (symbolVal k, fields (Just v)):kvs
    where Object kvs = fields (Just (Book m))
  cnst = undefined
  cnstM = undefined
  cnstS = undefined

test_fields :: Object PS.Action
test_fields = fields $ Just $ emptyBook
  & #name =: "name_value"
  & #age =: (66 :: Int)
  & #ntest =: (emptyBook
    & #bff =: True
  )
