{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Database.Generic where

import Data.Proxy

import GHC.Generics

import qualified Database.PostgreSQL.Simple.FromField as PS
import qualified Database.PostgreSQL.Simple.FromRow as PS

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

  cnst :: Object String -> Maybe (PS.ConvArray
  default cnst :: (Generic a, GFields (Rep a)) => Object String -> Maybe a
  cnst obj = to <$> gCnst obj

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

instance {-# OVERLAPPABLE #-} PS.FromField a => Fields a where
  fields _ = error "overlapping"
  cnst _ = error ""

instance {-# OVERLAPPABLE #-} Fields a => PS.FromRow a where
  fromRow = undefined

{-
instance (Fields a, Fields b) => Fields (a, b) where
  fields (Just (a, b)) = (,) <$> (fields (Just a) ++ fields (Just b))
-}

class GFields f where
  gFields :: Maybe (f a) -> Object String
  gCnst :: Object String -> Maybe (f a)

instance GFields f => GFields (D1 i f) where
  gFields (Just (M1 x)) = gFields (Just x)
  gFields Nothing = gFields (Nothing :: Maybe (f ()))
  gCnst obj = M1 <$> gCnst obj

instance (GFields f, Constructor c) => GFields (C1 c f) where
  gFields (Just (M1 x)) = Object (conName (undefined :: C1 c f ())) (getkvs (gFields (Just x)))
  gFields Nothing = Object (conName (undefined :: C1 c f ())) (getkvs (gFields (Nothing :: Maybe (f ()))))
  gCnst obj@(Object cnst _)
    | cnst == (conName (undefined :: C1 c f ())) = M1 <$> gCnst obj
  gCnst _ = Nothing

instance (Selector c, GFields f) => GFields (S1 c f) where
  gFields _ | null (selName (undefined :: S1 c f ())) = error "Types without record selectors not supported yet"
  gFields (Just (M1 x)) = Object "" [ (selName (undefined :: S1 c f ()), gFields (Just x))]
  gFields Nothing = Object "" [ (selName (undefined :: S1 c f ()), gFields (Nothing :: Maybe (f ())))]
  gCnst _ | null (selName (undefined :: S1 c f ())) = error "Types without record selectors not supported yet"
  gCnst obj@(Object _ kvs)
    | Just v <- lookup (selName (undefined :: S1 c f ())) kvs = M1 <$> gCnst v
  gCnst _ = Nothing

instance (GFields (Rep f), Fields f) => GFields (K1 R f) where
  gFields (Just (K1 x)) = fields (Just x)
  gFields Nothing = fields (Nothing :: Maybe f)
  gCnst obj = K1 <$> cnst obj

instance (GFields f, GFields g) => GFields (f :*: g) where
  gFields (Just (f :*: g)) = Object "" (getkvs (gFields (Just f)) ++ getkvs (gFields (Just g)))
  gFields Nothing = Object "" (getkvs (gFields (Nothing :: Maybe (f ()))) ++ getkvs (gFields (Nothing :: Maybe (g ()))))
  gCnst obj = (:*:) <$> gCnst obj <*> gCnst obj

instance (GFields f, GFields g) => GFields (f :+: g) where
  gFields (Just (L1 x)) = gFields (Just x)
  gFields (Just (R1 x)) = gFields (Just x)
  gFields Nothing = Object "" (getkvs (gFields (Nothing :: Maybe (f ()))) ++ getkvs (gFields (Nothing :: Maybe (g ()))))
  gCnst obj
    | Just x <- L1 <$> gCnst obj = Just x
    | Just x <- R1 <$> gCnst obj = Just x
    | otherwise = Nothing

instance GFields U1 where
  gFields _ = Empty
  gCnst _ = Nothing
