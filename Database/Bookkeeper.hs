{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Database.Bookkeeper where

import Control.Monad.Trans

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

type PersonB = Book
  '[ "name" :=> String
   , "age"  :=> Int
   , "nested" :=> (Book
     '[ "bff" :=> Bool ])
   ]

instance (Fields (Book' a)) => GFields (S1 c (K1 R (Book' a))) where
  gFields (Just (M1 (K1 f))) = fields (Just f)
  gFields Nothing = fields (Nothing :: Maybe (Book' a))
  gCnstS = fmap M1 <$> gCnstS

data A = A { number :: Int, person :: PersonB } deriving (Eq, Generic)

instance A.ToJSON A
instance A.ToJSON (Book' '[])
instance (A.ToJSON (Book' m), A.ToJSON v) => A.ToJSON (Book' (k :=> v ': m))
-- instance (A.ToJSON (Rep (Book' kvs) x)) => A.ToJSON (Book' kvs)

instance A.FromJSON A
instance A.FromJSON (Book' '[])
instance (A.FromJSON (Book' m), A.FromJSON v) => A.FromJSON (Book' (k :=> v ': m))

instance Generic (Book' '[]) where
  type Rep (Book' '[]) = U1
  from _ = U1
  to _   = Book (Map.Empty)

instance Generic (Book' (k :=> v ': m)) where
  -- type Rep (Book' (k :=> v ': m)) = S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 v) :*: Rep (Book' m)
  -- from (Book (Map.Ext k v m)) = M1 (K1 v) :*: from (Book m)
  -- to (M1 (K1 v) :*: m) = Book (Map.Ext (Map.Var :: Map.Var k) v (getBook (to m)))

  type Rep (Book' (k :=> v ': m)) = S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 v) :*: S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 (Book' m))
  from (Book (Map.Ext k v m)) = M1 (K1 v) :*: (M1 (K1 (Book m)))
  to (M1 (K1 v) :*: (M1 (K1 (Book m)))) = Book (Map.Ext (Map.Var :: Map.Var k) v m)

{-
type family ToRep a where
  ToRep (Book' (k :=> v ': m)) = S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 v) :*: ToRep (Book' m)
  ToRep (Book' '[]) = U1

instance Generic (Book' kvs) where
  type Rep (Book' kvs) = ToRep (Book' kvs)
  from (Book (Map.Ext k v m)) = M1 (K1 v) :*: from (Book m)
  -- to (M1 (K1 v) :*: m) = Book (Map.Ext (Map.Var :: Map.Var k) v (getBook (to m)))
-}

instance Fields (Book' '[]) where
  fields _ = Object []
  cnstS = return $ Just (Book Map.Empty)

instance (KnownSymbol k, Fields v, Fields (Book' m)) => Fields (Book' (k :=> v ': m)) where
  fields (Just (Book (Map.Ext k v m))) = Object $ (symbolVal k, fields (Just v)):kvs
    where Object kvs = fields (Just (Book m))
  fields Nothing = Object $ (symbolVal (Proxy :: Proxy k), fields (Nothing :: Maybe v)):kvs
    where Object kvs = fields (Nothing :: Maybe (Book' m))
  cnstS = do
    Just v <- cnstS
    Just m <- cnstS
    return (Just (Book (Map.Ext (Map.Var :: Map.Var k) v (getBook m))))

p = emptyBook
  & #name =: "name_value"
  & #age =: (66 :: Int)
  & #nested =: (emptyBook
    & #bff =: True
  )

{-
test_fields :: Object PS.Action
test_fields = fields $ Just $ emptyBook
  & #name =: "name_value"
  & #age =: (66 :: Int)
  & #nested =: (emptyBook
    & #bff =: True
  )
-}

