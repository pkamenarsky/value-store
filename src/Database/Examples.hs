{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Database.Examples where

import qualified Data.Aeson as A

import Bookkeeper hiding (Key, get, modify)
import Bookkeeper.Permissions hiding (modify, read, insert)

import qualified Data.List        as L
import Data.Typeable

import Database.Bookkeeper
import Database.Expr
import Database.Generic
import Database.Map
import Database.Query
import qualified Database.PostgreSQL.Simple as PS

import Prelude hiding (filter, sort, all, join)

import qualified Data.Type.Set as Set

import GHC.Generics

import Debug.Trace

data Admin = Admin
data Auth = Auth

type UndeadT = Book '[ "_kills" :=> Permission '[ "modify" :=> Admin ] Int ]

data Person' a = Person { _name :: String, _age :: Int }
               | Robot { _ai :: Bool }
               --  | Undead { _kills :: Int } deriving (Eq, Ord, Generic, Typeable, Show)
               | Undead a deriving (Eq, {- Ord, -} Generic, Typeable, Show)

type Person = Person' UndeadT

data Address = Address { _street :: String, _person :: Person } deriving (Generic, Typeable, Show)

instance A.FromJSON a => A.FromJSON (Person' a)
instance A.ToJSON a => A.ToJSON (Person' a)

instance A.FromJSON Address
instance A.ToJSON Address

instance Fields a => Fields (Person' a)
instance Fields Address

data Image = Horizontal { what :: Int } | Vertical { who :: Person, why :: String } deriving (Generic, Show)

instance Fields Image

killsE :: Expr (Person) Int
killsE = Fld "kills" $ \p -> case p of
  Undead p -> Just $ unsafeUnpackPermission $ p ?: #_kills
  _ -> Nothing

nameE :: Expr (Person) String
nameE = Fld "name" $ \p -> case p of
  p@Person{..} -> Just _name
  _ -> Nothing

ageE :: Expr (Person) Int
ageE = Fld "age" $ \p -> case p of
  p@Person{..} -> Just _age
  _ -> Nothing

aiE :: Expr (Person) Bool
aiE = Fld "ai" $ \p -> case p of
  p@Robot{..} -> Just _ai
  _ -> Nothing

personE :: Expr (Address) Person
personE = Fld "person" (Just . _person)

streetE :: Expr (Address) String
streetE = Fld "street" (Just . _street)

{-

ql = (filter (ageE `Grt` Cnst 3) $ sort nameE Nothing (Just 10) $ filter (ageE `Grt` Cnst 6) $ all)
qr :: Query (K (Key Person) Person)
qr = all
-- q1 :: _
q1 = {- join (Fst ageE `Grt` Snd (Fst ageE)) ql -} (join (Fst ageE `Grt` Snd ageE) ql qr)

q1sql = fst $ foldQuerySql (labelQuery q1)

-- q2 :: _ -- Query ((Person, Person), Person)
q2 = sort (Fst (Fst ageE)) Nothing (Just 100) $ join ((Fst (Fst ageE) `Eqs` Fst (Snd ageE)) `And` (Fst (Fst ageE) `Eqs` Cnst 222)) (join (Fst ageE `Eqs` Snd ageE) allPersons allPersons) (join (Fst (Fst ageE) `Eqs` Snd ageE) (join (Fst ageE `Eqs` Snd ageE) allPersons allPersons) allPersons)

-- q2sql = fst $ foldQuerySql (labelQuery q2)

allPersons :: Query (K (Key Person) Person)
allPersons = all

simplejoin = {- sort (Fst ageE) Nothing (Just 100) $ -} join (Fst ageE `Eqs` Snd ageE) allPersons allPersons
simplejoinai = {- sort (Fst ageE) Nothing (Just 100) $ -} join (Fst aiE `Eqs` Snd aiE) allPersons allPersons
simplejoinsql = fst $ foldQuerySql (labelQuery simplejoin)

-- simplejoinsbstsql = fst $ foldQuerySql $ labelQuery $ filter (substFst (Fst ageE `Grt` Snd ageE) (Person "name" 666)) allPersons

simple = filter (ageE `Grt` Cnst 7) $ filter (ageE `Grt` Cnst 7) $ {- join (Fst ageE `Grt` Snd ageE) allPersons -} (filter (ageE `Grt` Cnst 6) allPersons)
simplesql = fst $ foldQuerySql (labelQuery simple)

person :: Person
person = Undead $ emptyBook & #_kills =: unsafePermission 8

person1 = case person of
  Undead p -> Undead (p & #_kills =: unsafePermission 7)

test :: IO ()
test = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"

  -- modifyRow' conn (Admin `Set.Ext` Set.Empty) Database.Query.person $ \(p) ->
  --   case p of
  --     Undead p -> Undead (p & #_kills =: 7)

  modifyRow conn (Admin `Set.Ext` Set.Empty) (Key "key0" :: Key Person) $ \(p) ->
    case p of
      Undead p -> Undead (p & #_kills =: 9)

  -- rs <- PS.query_ conn "select cnst as a0_cnst, name as a0_name, age as a0_age, ai as a0_ai, kills as a0_kills from person" :: IO [W Person]
  -- traceIO $ show rs

  -- rs <- query conn (join (Fst aiE `Eqs` Snd (personE :+: aiE)) all (filter ((personE :+: aiE) `Eqs` Cnst True) all)) (traceIO . show)
  -- rs <- query conn simplejoinai (traceIO . show)
  rs <- query conn (filter (killsE `Eqs` Cnst 9) $ allPersons) (traceIO . show)
  -- rs <- query conn q2 (traceIO . show)
  -- rs <- query conn allPersons (traceIO . ("CB: "++ ) . show)

  print "--- Query"

  {-
  forM_ (fst rs) $ \p -> do
    case unK p of
      Undead p -> print (PRM.read (Admin `Set.Ext` Set.Empty) p)
      _ -> return ()
  -}

  -- traceIO $ show rs

  {-
  let rec  = (Person "john" 222)
      recr = Robot True

  insertRow conn "key3" recr

  let rec2 = (Address "doom" recr)

  insertRow conn "key2" rec2
  -}

  return ()

env :: IO (PS.Connection, Person, Address)
env = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"
  let p = Robot True
      a = Address "doom" p

  return (conn, p, a)

testSort :: IO ()
testSort = do
  conn <- PS.connectPostgreSQL "host=localhost port=5432 dbname='value'"

  insertRow conn ("key0") (Undead $ emptyBook & #_kills =: unsafePermission 5 :: Person)

  {-
  forM_ [0..10] $ \limit -> do
    PS.execute_ conn "delete from person"

    lock <- newMVar ()

    let q  -- = join (Fst ageE `Grt` Snd ageE) allPersons $ sort ageE (Just 0) (Just limit) $ filter ((ageE `Grt` Cnst 5)) allPersons
           = join (Fst ageE `Eqs` Snd ageE) allPersons $ sort ageE (Just 0) (Just limit) $ filter ((ageE `Grt` Cnst 5)) allPersons
             -- join (Fst ageE `Eqs` Snd ageE) allPersons allPersons
        cb rs = do
          rs' <- query_ conn q
          -- if (S.fromList rs /= S.fromList rs')
          if (rs /= rs')
            then do
              traceIO "Different results, expected: "
              traceIO $ show rs'
              traceIO "Received: "
              traceIO $ show rs
              traceIO "Difference: "
              -- traceIO $ show ((S.fromList rs' `S.difference` S.fromList rs) `S.union` (S.fromList rs `S.difference` S.fromList rs'))
              traceIO "Query: "
              traceIO $ show q
              error "Aborting"
            else do
              traceIO $ "Good, limit: " ++ show limit ++ ", size: " ++ show (length rs)
              takeMVar lock
    (_, tid) <- query conn q cb

    forM [0..20] $ \k -> do
      insertRow conn ("key" ++ show k) (Person "john" k)
      putMVar lock ()

    forM [0..20] $ \k -> do
      insertRow conn ("key" ++ show k) (Person "john" k)
      putMVar lock ()
      insertRow conn ("key" ++ show k) (Person "john" k)
      putMVar lock ()
      deleteRow conn ("key" ++ show k) (Proxy :: Proxy Person)
      putMVar lock ()
      deleteRow conn ("key" ++ show k) (Proxy :: Proxy Person)
      putMVar lock ()

    killThread tid
  -}
-}
