module Database.IxMap
  ( IxMap

  , empty
  , delete
  , insert
  , lookup
  , elemIndex
  , fromList
  , toList
  , size
  ) where

import Data.Function

import qualified Data.Map as M
import qualified Data.List as L

import Prelude hiding (take, lookup)
import qualified Prelude as P

data IxMap k a = IxMap [(k, a)] (a -> a -> Ordering) Int

instance (Show k, Show a) => Show (IxMap k a) where
  show (IxMap xs _ _) = show xs

empty :: (a -> a -> Ordering) -> IxMap k a
empty sort = IxMap [] sort maxBound

delete :: Ord k => k -> IxMap k a -> IxMap k a
delete k (IxMap xs sort limit) = IxMap (L.deleteBy ((==) `on` fst) (k, undefined) xs) sort limit

insert :: Ord k => k -> a -> IxMap k a -> IxMap k a
insert k a (IxMap xs sort limit) = IxMap (L.take limit $ L.insertBy (sort `on` snd) (k, a) xs) sort limit

lookup :: Ord k => k -> IxMap k a -> Maybe a
lookup k (IxMap xs _ _) = snd <$> (L.find ((k ==) . fst) xs)

elemIndex :: Ord k => k -> IxMap k a -> Maybe Int
elemIndex k (IxMap xs _ limit) = L.findIndex ((k ==) . fst) xs

fromList :: Ord k => (a -> a -> Ordering) -> Int -> [(k, a)] -> IxMap k a
fromList sort limit as = IxMap (L.sortBy (sort `on` snd) as) sort limit

toList :: IxMap k a -> [(k, a)]
toList (IxMap xs sort limit) = xs

size :: IxMap k a -> Int
size (IxMap xs _ limit) = L.length xs
