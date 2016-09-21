module Database.IxMap
  ( IxMap

  , empty
  , delete
  , insert
  , lookup
  , take
  , elemIndex
  , fromList
  , toList
  ) where

import Data.Function

import qualified Data.Map as M
import qualified Data.List as L

import Prelude hiding (take, lookup)
import qualified Prelude as P

data IxMap k a = IxMap (M.Map k a) (a -> a -> Ordering) Int

instance (Show k, Show a) => Show (IxMap k a) where
  show (IxMap as _ _) = show as

empty :: (a -> a -> Ordering) -> IxMap k a
empty sort = IxMap M.empty sort maxBound

delete :: Ord k => k -> IxMap k a -> IxMap k a
delete k (IxMap as sort limit) = IxMap (M.delete k as) sort limit

insert :: Ord k => k -> a -> IxMap k a -> IxMap k a
insert k a (IxMap as sort limit) = IxMap (M.insert k a as) sort limit

lookup :: Ord k => k -> IxMap k a -> Maybe a
lookup k m = snd <$> (L.find ((k ==) . fst) $ toList m)

elemIndex :: Ord k => k -> IxMap k a -> Maybe Int
elemIndex k m = L.elemIndex k $ map fst $ toList m

take :: Int -> IxMap k a -> IxMap k a
take n (IxMap as sort limit) = IxMap as sort (min n limit)

fromList :: Ord k => [(k, a)] -> (a -> a -> Ordering) -> IxMap k a
fromList as sort = IxMap (M.fromList as) sort maxBound

toList :: IxMap k a -> [(k, a)]
toList (IxMap as sort limit) = P.take limit $ L.sortBy (sort `on` snd) $ M.toList as
