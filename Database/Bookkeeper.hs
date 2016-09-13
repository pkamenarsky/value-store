{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Database.Bookkeeper where

import Bookkeeper
import Bookkeeper.Internal

import Data.Type.Bool
import Data.Type.Equality

import Data.Proxy

import qualified Data.ByteString.Char8 as BC

import Database.Generic

import qualified Data.Aeson as A

import qualified Database.PostgreSQL.Simple.FromField as PS
import qualified Database.PostgreSQL.Simple.ToField as PS
import qualified Database.PostgreSQL.Simple.FromRow as PS
import qualified Database.PostgreSQL.Simple.ToRow as PS
import qualified Database.PostgreSQL.Simple.Internal as PS

import qualified Data.Type.Map as Map

import GHC.Generics
import GHC.OverloadedLabels
import GHC.TypeLits

type Person = Book
  '[ "name" :=> String
   , "age"  :=> Int
   , "nested" :=> (Book
     '[ "bff" :=> Bool ])
   ]

data A = A { number :: Int, person :: Person } deriving Generic

instance A.ToJSON (Book' kvs)
instance A.ToJSON A

{-
instance Generic (Book' '[]) where
  type Rep (Book' '[]) = U1
  from _ = U1
  to _   = Book (Map.Empty)

instance (Generic (Book' m)) => Generic (Book' (k :=> v ': m)) where
  type Rep (Book' (k :=> v ': m)) = S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 v) :*: Rep (Book' m)
  from (Book (Map.Ext k v m)) = M1 (K1 v) :*: from (Book m)
  to (M1 (K1 v) :*: m) = Book (Map.Ext (Map.Var :: Map.Var k) v (getBook (to m)))
-}

instance Generic (Book' kvs) where
  type Rep (Book' kvs) = S1 ('MetaSel ('Just "asd") 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 String)

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

p = emptyBook
  & #name =: "name_value"
  & #age =: (66 :: Int)
  & #nested =: (emptyBook
    & #bff =: True
  )

test_fields :: Object PS.Action
test_fields = fields $ Just $ emptyBook
  & #name =: "name_value"
  & #age =: (66 :: Int)
  & #nested =: (emptyBook
    & #bff =: True
  )

