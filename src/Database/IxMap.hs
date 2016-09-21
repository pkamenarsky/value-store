module Database.IxMap
  ( IxMap

  , empty
  , delete
  , insert
  ) where

data IxMap a = IxMap [a] (a -> a -> Ordering) (a -> a -> Ordering)

instance Show a => Show (IxMap a) where
  show (IxMap as _ _) = show as

empty :: (a -> a -> Ordering) -> (a -> a -> Ordering) -> IxMap a
empty key sort = IxMap [] key sort

deleteByKey :: (a -> Bool) -> [a] -> [a]
deleteByKey f [] = []
deleteByKey f (x:xs)
  | f x = deleteByKey f xs
  | otherwise = x:deleteByKey f xs

delete :: a -> IxMap a -> IxMap a
delete a (IxMap as key sort) = IxMap (deleteByKey ((EQ ==) . key a) as) key sort

insertBy' :: (a -> a -> Ordering) -> Int -> a -> [a] -> (Int, [a])
insertBy' _   i x [] = (i, [x])
insertBy' cmp i x ys@(y:ys')
 = case cmp x y of
     GT -> let (i', ys'') = insertBy' cmp (i + 1) x ys' in (i', y : ys'')
     _  -> (i, x : ys)

insertByKey :: (a -> a -> Ordering) -> (a -> a -> Ordering) -> a -> [a] -> (Int, [a])
insertByKey key sort x = insertBy' sort 0 x . deleteByKey ((EQ ==) . key x)

insert :: a -> IxMap a -> (Int, IxMap a)
insert a (IxMap as key sort) = (i, IxMap as' key sort)
  where (i, as') = insertByKey key sort a as
