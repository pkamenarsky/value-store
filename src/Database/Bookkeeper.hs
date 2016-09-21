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
import Bookkeeper.Permissions
import Bookkeeper.Internal

import Data.Type.Bool
import Data.Type.Equality

import Data.Proxy
import Data.Text as T
import Data.HashMap.Strict as H

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

instance (A.FromJSON a) => A.FromJSON (Permission (prf ) a)
instance (A.ToJSON a)   => A.ToJSON (Permission (prf :: [Map.Mapping Symbol *]) a)

instance (PS.ToField a) => PS.ToField (Permission (prf :: [Map.Mapping Symbol *]) a) where
  toField a = PS.toField (unsafeUnpackPermission a)

instance (PS.FromField a) => PS.FromField (Permission (prf :: [Map.Mapping Symbol *]) a) where
  fromField f dat = unsafePermission <$> PS.fromField f dat

--------------------------------------------------------------------------------


instance A.ToJSON (Book' '[]) where
  toJSON _ = A.Null
instance (KnownSymbol k, A.ToJSON (Book' m), A.ToJSON v) => A.ToJSON (Book' (k :=> v ': m)) where
  toJSON (Book (Map.Ext k v m)) = case A.toJSON (Book m) of
    A.Object kvs -> A.Object $
      H.fromList [ (T.pack (symbolVal k), A.toJSON v) ] `H.union` kvs
    _ -> A.Object $ H.fromList [ (T.pack (symbolVal k), A.toJSON v) ]

instance A.FromJSON (Book' '[]) where
  parseJSON _ = return (Book Map.Empty)
instance (KnownSymbol k, A.FromJSON v, A.FromJSON (Book' m)) => A.FromJSON (Book' (k :=> v ': m)) where
  parseJSON o'@(A.Object o) = do
    v <- o A..: T.pack (symbolVal (Proxy :: Proxy k))
    Book m' <- A.parseJSON o'
    return $ Book (Map.Ext (Map.Var :: Map.Var k) v m')

instance Generic (Book' '[]) where
  type Rep (Book' '[]) = U1
  from _ = U1
  to _   = Book (Map.Empty)

instance (Generic (Book' m)) => Generic (Book' (k :=> v ': m)) where
  type Rep (Book' (k :=> v ': m)) = S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 v) :*: Rep (Book' m)
  from (Book (Map.Ext k v m)) = M1 (K1 v) :*: from (Book m)
  to (M1 (K1 v) :*: m) = Book (Map.Ext (Map.Var :: Map.Var k) v (getBook (to m)))

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

p :: PersonB
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

