{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Database.Generic where

import Control.Monad.Trans

import Data.Proxy

import GHC.Generics

import qualified Data.ByteString as B

import qualified Database.PostgreSQL.Simple.FromField as PS
import qualified Database.PostgreSQL.Simple.FromRow as PS
import qualified Database.PostgreSQL.Simple.Internal as PS

data Object a = Empty
              | Value a
              | Object String [(String, Object a)]
              deriving Show

flattenObject :: String -> Object String -> [(String, String)]
flattenObject prefix Empty     = []
flattenObject prefix (Value v) = [(prefix, v)]
flattenObject prefix (Object cnst kvs) = concat
  [ flattenObject (prefix' k i) v
  | (i, (k, v)) <- zip [0..] (("cnst", Value ("'" ++ cnst ++ "'")):kvs)
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
getkvs (Object _ kvs) = kvs
getkvs Empty          = []
getkvs _              = error "getkvs: Value"

-- TODO: count in g* or disallow empty selectors

class Fields a where
  fields :: Maybe a -> Object String
  default fields :: (Generic a, GFields (Rep a)) => Maybe a -> Object String
  fields (Just a) = gFields $ Just $ from a
  fields Nothing  = gFields $ (Nothing :: Maybe (Rep a ()))

  cnst :: Object (PS.Field, Maybe B.ByteString) -> Maybe (PS.Conversion a)
  default cnst :: (Generic a, GFields (Rep a)) => Object (PS.Field, Maybe B.ByteString) -> Maybe (PS.Conversion a)
  cnst obj = fmap to <$> gCnst obj

{-
instance Fields Char where
  fields Nothing  = Value ""
  fields (Just v) = Value (show v)
  cnst (Value [v]) = Just v
  cnst _ = Nothing

instance Fields String where
  fields Nothing  = Value ""
  fields (Just v) = Value v
  cnst (Value v) = Just v
  cnst _ = Nothing

instance Fields Int where
  fields Nothing  = Value ""
  fields (Just v) = Value (show v)
  cnst (Value v) = Just $ read v
  cnst _ = Nothing
-}

instance {-# OVERLAPPABLE #-} PS.FromField a => Fields a where
  fields _ = error "overlapping"
  cnst (Value (f, bs)) = Just (PS.fromField f bs)
  cnst _ = Nothing

instance {-# OVERLAPPABLE #-} Fields a => PS.FromRow a where
  fromRow = PS.RP $ case (cnst undefined) of
    Just x  -> lift $ lift x
    Nothing -> lift $ lift $ PS.conversionError (PS.ConversionFailed "" Nothing "" "" "")

{-
instance (Fields a, Fields b) => Fields (a, b) where
  fields (Just (a, b)) = (,) <$> (fields (Just a) ++ fields (Just b))
-}

class GFields f where
  gFields :: Maybe (f a) -> Object String
  gCnst :: Object (PS.Field, Maybe B.ByteString) -> Maybe (PS.Conversion (f a))

instance GFields f => GFields (D1 i f) where
  gFields (Just (M1 x)) = gFields (Just x)
  gFields Nothing = gFields (Nothing :: Maybe (f ()))
  gCnst obj = fmap M1 <$> gCnst obj

instance (GFields f, Constructor c) => GFields (C1 c f) where
  gFields (Just (M1 x)) = Object (conName (undefined :: C1 c f ())) (getkvs (gFields (Just x)))
  gFields Nothing = Object (conName (undefined :: C1 c f ())) (getkvs (gFields (Nothing :: Maybe (f ()))))
  gCnst obj@(Object cnst _)
    | cnst == (conName (undefined :: C1 c f ())) = fmap M1 <$> gCnst obj
  gCnst _ = Nothing

instance (Selector c, GFields f) => GFields (S1 c f) where
  gFields _ | null (selName (undefined :: S1 c f ())) = error "Types without record selectors not supported yet"
  gFields (Just (M1 x)) = Object "" [ (selName (undefined :: S1 c f ()), gFields (Just x))]
  gFields Nothing = Object "" [ (selName (undefined :: S1 c f ()), gFields (Nothing :: Maybe (f ())))]
  gCnst _ | null (selName (undefined :: S1 c f ())) = error "Types without record selectors not supported yet"
  gCnst obj@(Object _ kvs)
    | Just v <- lookup (selName (undefined :: S1 c f ())) kvs = fmap M1 <$> gCnst v
  gCnst _ = Nothing

instance (GFields (Rep f), Fields f) => GFields (K1 R f) where
  gFields (Just (K1 x)) = fields (Just x)
  gFields Nothing = fields (Nothing :: Maybe f)
  gCnst obj = fmap K1 <$> cnst obj

instance (GFields f, GFields g) => GFields (f :*: g) where
  gFields (Just (f :*: g)) = Object "" (getkvs (gFields (Just f)) ++ getkvs (gFields (Just g)))
  gFields Nothing = Object "" (getkvs (gFields (Nothing :: Maybe (f ()))) ++ getkvs (gFields (Nothing :: Maybe (g ()))))
  -- gCnst obj = (:*:) <$> gCnst obj <*> gCnst obj
  gCnst obj = undefined

instance (GFields f, GFields g) => GFields (f :+: g) where
  gFields (Just (L1 x)) = gFields (Just x)
  gFields (Just (R1 x)) = gFields (Just x)
  gFields Nothing = Object "" (getkvs (gFields (Nothing :: Maybe (f ()))) ++ getkvs (gFields (Nothing :: Maybe (g ()))))
  gCnst obj
    | Just x <- fmap L1 <$> gCnst obj = Just x
    | Just x <- fmap R1 <$> gCnst obj = Just x
    | otherwise = Nothing

instance GFields U1 where
  gFields _ = Empty
  gCnst _ = Nothing
