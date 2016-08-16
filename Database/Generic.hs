{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Database.Generic where

import Data.Proxy

import GHC.Generics

data Object = Empty
            | Value String
            | Object String [(String, Object)]
            deriving Show

flattenObject :: String -> Object -> [(String, String)]
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

getkvs :: Object -> [(String, Object)]
getkvs (Object _ kvs) = kvs
getkvs Empty          = []
getkvs _              = error "getkvs: Value"

class Fields a where
  fields :: Maybe a -> Object
  default fields :: (Generic a, GFields (Rep a)) => Maybe a -> Object
  fields (Just a) = gFields $ Just $ from a
  fields Nothing  = gFields $ (Nothing :: Maybe (Rep a ()))

instance Fields Char where
  fields Nothing  = Value ""
  fields (Just v) = Value (show v)

instance Fields String where
  fields Nothing  = Value ""
  fields (Just v) = Value ("'" ++ v ++ "'")

instance Fields Int where
  fields Nothing  = Value ""
  fields (Just v) = Value (show v)

class GFields f where
  gFields :: Maybe (f a) -> Object

instance GFields f => GFields (D1 i f) where
  gFields (Just (M1 x)) = gFields (Just x)
  gFields Nothing = gFields (Nothing :: Maybe (f ()))

instance (GFields f, Constructor c) => GFields (C1 c f) where
  gFields (Just (M1 x)) = Object (conName (undefined :: C1 c f ())) (getkvs (gFields (Just x)))
  gFields Nothing = Object (conName (undefined :: C1 c f ())) (getkvs (gFields (Nothing :: Maybe (f ()))))

instance (Selector c, GFields f) => GFields (S1 c f) where
  gFields (Just (M1 x)) = Object "" [ (selName (undefined :: S1 c f ()), gFields (Just x))]
  gFields Nothing = Object "" [ (selName (undefined :: S1 c f ()), gFields (Nothing :: Maybe (f ())))]

instance (GFields (Rep f), Fields f) => GFields (K1 R f) where
  gFields (Just (K1 x)) = fields (Just x)
  gFields Nothing = fields (Nothing :: Maybe f)

instance (GFields f, GFields g) => GFields (f :*: g) where
  gFields (Just (f :*: g)) = Object "" (getkvs (gFields (Just f)) ++ getkvs (gFields (Just g)))
  gFields Nothing = Object "" (getkvs (gFields (Nothing :: Maybe (f ()))) ++ getkvs (gFields (Nothing :: Maybe (g ()))))

instance (GFields f, GFields g) => GFields (f :+: g) where
  gFields (Just (L1 x)) = gFields (Just x)
  gFields (Just (R1 x)) = gFields (Just x)
  gFields Nothing = Object "" (getkvs (gFields (Nothing :: Maybe (f ()))) ++ getkvs (gFields (Nothing :: Maybe (g ()))))

instance GFields U1 where
  gFields _ = Empty