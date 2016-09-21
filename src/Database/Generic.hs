{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Database.Generic where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict

import Control.Applicative ((<|>))

import Data.Maybe
import Data.Proxy

import GHC.Generics
import System.IO.Unsafe

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC

import qualified Database.PostgreSQL.Simple.FromField as PS
import qualified Database.PostgreSQL.Simple.ToField as PS
import qualified Database.PostgreSQL.Simple.FromRow as PS
import qualified Database.PostgreSQL.Simple.ToRow as PS
import qualified Database.PostgreSQL.Simple.Internal as PS

import qualified Database.PostgreSQL.LibPQ as PQ

import Debug.Trace

data Object a = Empty
              | Value a
              | Object [(String, Object a)]
              -- | Sum (Object a) (Object a)
              deriving (Show, Functor, Foldable, Traversable)

flattenObject :: String -> Object a -> [(String, a)]
flattenObject prefix Empty     = []
flattenObject prefix (Value v) = [(prefix, v)]
flattenObject prefix (Object kvs) = concat
  [ flattenObject (prefix' k i) v
  | (i, (k, v)) <- zip [0..] kvs
  ]
  where
    prefix' k i
           | null prefix   = k' k i
           | otherwise     = prefix ++ "_" ++ k' k i

    k' k i | null k        = show i
           | ('_':ks) <- k = ks
           | otherwise     = k

--------------------------------------------------------------------------------

getkvs :: Object a -> [(String, Object a)]
getkvs (Object kvs) = kvs
getkvs Empty        = []
getkvs _            = error "getkvs: Value"

class Fields a where
  fields :: Maybe a -> Object PS.Action
  default fields :: (Generic a, GFields (Rep a)) => Maybe a -> Object PS.Action
  fields (Just a) = gFields $ Just $ from a
  fields Nothing  = gFields $ (Nothing :: Maybe (Rep a ()))

  cnstS :: StateT String PS.RowParser (Maybe a)
  default cnstS :: (Generic a, GFields (Rep a)) => StateT String PS.RowParser (Maybe a)
  cnstS = fmap to <$> gCnstS

instance PS.ToField Char where
  toField x = PS.toField [x]

instance {-# OVERLAPPABLE #-} (PS.FromField a, PS.ToField a) => Fields a where
  fields (Just v) = Value (PS.toField v)
  fields Nothing  = Value (PS.toField "")
  cnstS = lift $ PS.field

instance {-# OVERLAPPABLE #-} Fields a => PS.ToRow a where
  toRow v = map snd $ flattenObject "" $ fields (Just v)

instance {-# OVERLAPPABLE #-} Fields a => PS.FromRow a where
  fromRow = do
    a <- fromMaybe (error "Can't parse") <$> evalStateT cnstS ""
    return a

class GFields f where
  gFields :: Maybe (f a) -> Object PS.Action
  gCnstS :: StateT String PS.RowParser (Maybe (f a))

instance GFields f => GFields (D1 i f) where
  gFields (Just (M1 x)) = gFields (Just x)
  gFields Nothing = gFields (Nothing :: Maybe (f ()))
  gCnstS = do
    cnst <- lift $ PS.field
    put cnst
    fmap M1 <$> gCnstS

instance (GFields f, Constructor c) => GFields (C1 c f) where
  gFields (Just (M1 x)) = Object (("cnst", Value (PS.Escape $ BC.pack $ conName (undefined :: C1 c f ()))):getkvs (gFields (Just x)))
  gFields Nothing = Object (("cnst", Value (PS.Escape $ BC.pack $ conName (undefined :: C1 c f ()))):getkvs (gFields (Nothing :: Maybe (f ()))))
  gCnstS = fmap M1 <$> gCnstS

instance {-# OVERLAPPABLE #-} (Selector c, GFields f) => GFields (S1 c f) where
  -- gFields _ | null (selName (undefined :: S1 c f ())) = error "Types without record selectors not supported yet"
  gFields (Just (M1 x)) | null (selName (undefined :: S1 c f ())) = gFields (Just x)
  gFields (Just (M1 x)) = Object [ (selName (undefined :: S1 c f ()), gFields (Just x))]
  gFields Nothing | null (selName (undefined :: S1 c f ())) = gFields (Nothing :: Maybe (f ()))
  gFields Nothing = Object [ (selName (undefined :: S1 c f ()), gFields (Nothing :: Maybe (f ())))]
  gCnstS = fmap M1 <$> gCnstS

instance ({-GFields (Rep f),-} Fields f) => GFields (K1 R f) where
  gFields (Just (K1 x)) = fields (Just x)
  gFields Nothing = fields (Nothing :: Maybe f)
  gCnstS = fmap K1 <$> cnstS

instance (GFields f, GFields g) => GFields (f :*: g) where
  gFields (Just (f :*: g)) = Object (getkvs (gFields (Just f)) ++ getkvs (gFields (Just g)))
  gFields Nothing = Object (getkvs (gFields (Nothing :: Maybe (f ()))) ++ getkvs (gFields (Nothing :: Maybe (g ()))))
  gCnstS = do
    a <- gCnstS
    b <- gCnstS
    return $ fmap (:*:) a <*> b

instance (GFields f, GFields g) => GFields (f :+: g) where
  gFields (Just (L1 x)) = gFields (Just x)
  gFields (Just (R1 x)) = gFields (Just x)
  gFields Nothing = Object (getkvs (gFields (Nothing :: Maybe (f ()))) ++ filter ((/= "cnst") . fst) (getkvs (gFields (Nothing :: Maybe (g ())))))
  gCnstS = do
    x <- fmap L1 <$> gCnstS
    y <- fmap R1 <$> gCnstS
    return $ x <|> y

instance GFields U1 where
  gFields _ = Empty
  gCnstS = return Nothing
