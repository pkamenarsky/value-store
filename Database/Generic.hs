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
           -- | ('_':ks) <- k = ks
           | otherwise     = k

-- Get fields only -------------------------------------------------------------

class Fields a where
  fields :: Proxy a -> Object
  default fields :: (Generic a, GFields (Rep a)) => Proxy a -> Object
  fields _ = gFields (undefined :: Rep a ())

instance Fields Char where
  fields _ = Value ""

instance Fields String where
  fields _ = Value ""

instance Fields Int where
  fields _ = Value ""

class GFields f where
  gFields :: f a -> Object

instance GFields f => GFields (D1 i f) where
  gFields _ = gFields (undefined :: f ())

instance (GFields f, Constructor c) => GFields (C1 c f) where
  gFields _ = Object (conName (undefined :: C1 c f ())) (get (gFields (undefined :: f ())))
    where get (Object _ kvs) = kvs
          get Empty = []
          get _ = error "C1 returned Value"

instance (Selector c, GFields f) => GFields (S1 c f) where
  gFields _ = Object "" [ (selName (undefined :: S1 c f ()), gFields (undefined :: f ()))]

instance (GFields (Rep f), Fields f) => GFields (K1 R f) where
  gFields _ = fields (Proxy :: Proxy f)

instance (GFields f, GFields g) => GFields (f :*: g) where
  gFields _ = Object "" (get (gFields (undefined :: f ())) ++ get (gFields (undefined :: g ())))
    where get (Object _ kvs) = kvs
          get Empty = []
          get _ = error "gToRow returned value"

instance (GFields f, GFields g) => GFields (f :+: g) where
  gFields _ = Object "" (get (gFields (undefined :: f ())) ++ get (gFields (undefined :: g ())))
    where get (Object _ kvs) = kvs
          get Empty = []
          get _ = error "gToRow returned value"

instance GFields U1 where
  gFields _ = Empty

-- Get fields and values -------------------------------------------------------

class DBRow a where
  toRow :: a -> Object
  default toRow :: (Generic a, GDBRow (Rep a)) => a -> Object
  toRow = gToRow . from

instance (DBRow a, DBRow b) => DBRow (a, b) where
  toRow (a, b) = Object "," [("fst", toRow a), ("snd", toRow b)]

instance DBRow Char where
  toRow x = Value (show x)

instance DBRow String where
  toRow x = Value ("'" ++ x ++ "'")

instance DBRow Int where
  toRow x = Value (show x)

class GDBRow f where
  gToRow :: f a -> Object
  -- gFromRow :: (Int, [(String, String)]) -> Maybe a

instance GDBRow U1 where
  gToRow U1 = Empty

instance GDBRow f => GDBRow (D1 i f) where
  gToRow (M1 x) = gToRow x

instance (GDBRow f, Constructor c) => GDBRow (C1 c f) where
  gToRow (M1 x) = Object (conName (undefined :: C1 c f ())) (get (gToRow x))
    where get (Object _ kvs) = kvs
          get Empty = []
          get _ = error "C1 returned Value"

instance (Selector s, GDBRow f) => GDBRow (S1 s f) where
  gToRow (M1 x) = Object "" [ (selName (undefined :: S1 s f ()), gToRow x) ]

instance (GDBRow (Rep f), DBRow f) => GDBRow (K1 R f) where
  gToRow (K1 x) = toRow x

instance (GDBRow f, GDBRow g) => GDBRow (f :*: g) where
  gToRow (f :*: g) = Object "" (get (gToRow f) ++ get (gToRow g))
    where get (Object _ kvs) = kvs
          get Empty = []
          get _ = error "gToRow returned value"

instance (GDBRow f, GDBRow g) => GDBRow (f :+: g) where
  gToRow (L1 x) = gToRow x
  gToRow (R1 x) = gToRow x
