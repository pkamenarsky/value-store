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

  cnst :: Object (PS.Field, Maybe B.ByteString) -> Maybe (PS.Conversion a)
  default cnst :: (Generic a, GFields (Rep a)) => Object (PS.Field, Maybe B.ByteString) -> Maybe (PS.Conversion a)
  cnst obj = fmap to <$> gCnst obj

  cnstM :: Object PS.Action -> Maybe (PS.RowParser a)
  default cnstM :: (Generic a, GFields (Rep a)) => Object PS.Action -> Maybe (PS.RowParser a)
  cnstM obj = fmap to <$> gCnstM obj

  cnstS :: StateT String PS.RowParser (Maybe a)
  default cnstS :: (Generic a, GFields (Rep a)) => StateT String PS.RowParser (Maybe a)
  cnstS = fmap to <$> gCnstS

instance PS.ToField Char where
  toField x = PS.toField [x]

instance {-# OVERLAPPABLE #-} (PS.FromField a, PS.ToField a) => Fields a where
  fields (Just v) = Value (PS.toField v)
  fields Nothing  = Value (PS.toField "")
  cnst (Value (f, bs)) = Just (PS.fromField f bs)
  cnst _ = Nothing
  cnstM (Value _) = Just PS.field
  cnstM _ = Nothing
  cnstS = lift $ PS.field

instance {-# OVERLAPPABLE #-} Fields a => PS.ToRow a where
  toRow v = map snd $ flattenObject "" $ fields (Just v)

class GFields f where
  gFields :: Maybe (f a) -> Object PS.Action
  gCnst :: Object (PS.Field, Maybe B.ByteString) -> Maybe (PS.Conversion (f a))
  gCnstM :: Object PS.Action -> Maybe (PS.RowParser (f a))
  gCnstS :: StateT String PS.RowParser (Maybe (f a))

instance GFields f => GFields (D1 i f) where
  gFields (Just (M1 x)) = gFields (Just x)
  gFields Nothing = gFields (Nothing :: Maybe (f ()))
  gCnst obj = fmap M1 <$> gCnst obj
  gCnstM obj = fmap M1 <$> gCnstM obj
  gCnstS = do
    cnst <- lift $ PS.field
    put cnst
    fmap M1 <$> gCnstS

instance (GFields f, Constructor c) => GFields (C1 c f) where
  gFields (Just (M1 x)) = Object (("cnst", Value (PS.Escape $ BC.pack $ conName (undefined :: C1 c f ()))):getkvs (gFields (Just x)))
  gFields Nothing = Object (("cnst", Value (PS.Escape $ BC.pack $ conName (undefined :: C1 c f ()))):getkvs (gFields (Nothing :: Maybe (f ()))))
  gCnst obj@(Object kvs)
    | Just (Value (_, Just cnst)) <- lookup "cnst" kvs
    , BC.unpack cnst == (conName (undefined :: C1 c f ())) = fmap M1 <$> gCnst obj
  gCnst _ = Nothing
  gCnstM obj@(Object kvs)
    | Just (Value (PS.Escape cnst)) <- lookup "cnst" kvs
    , BC.unpack cnst == (conName (undefined :: C1 c f ())) = do
      x <- fmap M1 <$> gCnstM obj
      return ((PS.field :: PS.RowParser String) >> x)
  gCnstM _ = Nothing
  gCnstS = fmap M1 <$> gCnstS

instance (Selector c, GFields f) => GFields (S1 c f) where
  gFields _ | null (selName (undefined :: S1 c f ())) = error "Types without record selectors not supported yet"
  gFields (Just (M1 x)) = Object [ (selName (undefined :: S1 c f ()), gFields (Just x))]
  gFields Nothing = Object [ (selName (undefined :: S1 c f ()), gFields (Nothing :: Maybe (f ())))]
  gCnst _ | null (selName (undefined :: S1 c f ())) = error "Types without record selectors not supported yet"
  gCnst obj@(Object kvs)
    | Just v <- lookup (selName (undefined :: S1 c f ())) kvs = fmap M1 <$> gCnst v
  gCnst _ = Nothing
  gCnstM _ | null (selName (undefined :: S1 c f ())) = error "Types without record selectors not supported yet"
  gCnstM obj@(Object kvs)
    | Just v <- lookup (selName (undefined :: S1 c f ())) kvs = fmap M1 <$> gCnstM v
  gCnstM _ = Nothing
  gCnstS = fmap M1 <$> gCnstS

instance (GFields (Rep f), Fields f) => GFields (K1 R f) where
  gFields (Just (K1 x)) = fields (Just x)
  gFields Nothing = fields (Nothing :: Maybe f)
  gCnst obj = fmap K1 <$> cnst obj
  gCnstM obj = fmap K1 <$> cnstM obj
  gCnstS = fmap K1 <$> cnstS

instance (GFields f, GFields g) => GFields (f :*: g) where
  gFields (Just (f :*: g)) = Object (getkvs (gFields (Just f)) ++ getkvs (gFields (Just g)))
  gFields Nothing = Object (getkvs (gFields (Nothing :: Maybe (f ()))) ++ getkvs (gFields (Nothing :: Maybe (g ()))))
  gCnst obj = do
    a <- gCnst obj
    b <- gCnst obj
    return $ fmap (:*:) a <*> b
  gCnstM obj = do
    a <- gCnstM obj
    b <- gCnstM obj
    return $ fmap (:*:) a <*> b
  gCnstS = do
    a <- gCnstS
    b <- gCnstS
    return $ fmap (:*:) a <*> b

instance (GFields f, GFields g) => GFields (f :+: g) where
  gFields (Just (L1 x)) = gFields (Just x)
  gFields (Just (R1 x)) = gFields (Just x)
  gFields Nothing = Object (getkvs (gFields (Nothing :: Maybe (f ()))) ++ filter ((/= "cnst") . fst) (getkvs (gFields (Nothing :: Maybe (g ())))))
  gCnst obj
    | Just x <- fmap L1 <$> gCnst obj = Just x
    | Just x <- fmap R1 <$> gCnst obj = Just x
  gCnst _ = Nothing
  gCnstM obj
    | Just x <- fmap L1 <$> gCnstM obj = Just x
    | Just x <- fmap R1 <$> gCnstM obj = Just x
  gCnstM _ = Nothing
  gCnstS = do
    x <- fmap L1 <$> gCnstS
    y <- fmap R1 <$> gCnstS
    return $ x <|> y

instance GFields U1 where
  gFields _ = Empty
  gCnst _ = Nothing
  gCnstM _ = Nothing
  gCnstS = return Nothing
