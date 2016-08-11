{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module Database.Query where

import Control.Monad.State hiding (join)

import Data.Maybe
import Data.List                  (intersperse)
import Data.Ord

import Data.Tree

import Prelude hiding (filter, sort, all, join)

import Debug.Trace

insertBy' :: (a -> a -> Ordering) -> a -> [a] -> Int -> (Int, [a])
insertBy' _   x [] i = (i, [x])
insertBy' cmp x ys@(y:ys') i
 = case cmp x y of
     GT -> let (i', ys'') = insertBy' cmp x ys' (i + 1) in (i', y : ys'')
     _  -> (i, x : ys)

--------------------------------------------------------------------------------

data Label r a =
    Label String (r -> a)
  -- | forall s. Compose (Label r s) (Label s a)
    deriving Show

data Expr r a where
  Cnst :: Show a => a -> Expr r a
  Fld  :: String -> (r -> a) -> Expr r a
  Fst  :: Show a => Expr r a -> Expr (r, s) a
  Snd  :: Show a => Expr s a -> Expr (r, s) a
  And  :: Expr r Bool -> Expr r Bool -> Expr r Bool
  Grt  :: Expr r Int -> Expr r Int -> Expr r Bool
  Plus :: Expr r Int -> Expr r Int -> Expr r Int

instance Show (a -> b) where
  show _ = "(a -> b)"

deriving instance Show (Expr r a)

genVar :: State Int String
genVar = do
  i <- get
  modify (+1)
  return $ "a" ++ show i

brackets :: String -> String
brackets str = "(" ++ str ++ ")"

type Ctx = Tree [(Maybe String, String)]

foldExprSql' :: Ctx -> Expr r a -> String
foldExprSql' ctx (Cnst a) = show a
foldExprSql' ctx (Fld name _) =
  case [ var | var <- rootLabel ctx, name == snd var ] of
    [(Just alias, var)] -> alias ++ "_" ++ var
    [(Nothing, var)]    -> var
    []                  -> error "No such var"
    _                   -> error "More than one var"
foldExprSql' ctx (Fst q) = foldExprSql' (head $ subForest ctx) q
foldExprSql' ctx (Snd q) = foldExprSql' (last $ subForest ctx) q
foldExprSql' ctx (And a b) = brackets $ foldExprSql' ctx a ++ " and " ++ foldExprSql' ctx b
foldExprSql' ctx (Grt a b) = brackets $ foldExprSql' ctx a ++ " > " ++ foldExprSql' ctx b
foldExprSql' ctx (Plus a b) = brackets $ foldExprSql' ctx a ++ " + " ++ foldExprSql' ctx b

data QueryCache a = QueryCache [a] deriving Show

data Row = Row String [String] deriving Show

data Query' a l where
  All    :: l -> Row -> Query' a l
  Filter :: l -> Expr a Bool -> Query' a l -> Query' a l
  Sort   :: Ord b => l -> QueryCache a -> Label a b -> Maybe Int -> Query' a l -> Query' a l
  Join   :: (Show a, Show b) => l -> Expr (a, b) Bool -> Query' a l -> Query' b l -> Query' (a, b) l

deriving instance (Show l, Show a) => Show (Query' a l)

type Query a = Query' a ()
type LQuery a = Query' a String

all :: Row -> Query a
all = All ()

filter :: Expr a Bool -> Query a -> Query a
filter = Filter ()

sort :: Ord b => Label a b -> Maybe Int -> Query a -> Query a
sort = Sort () (QueryCache [])

join :: (Show a, Show b) => Expr (a, b) Bool -> Query a -> Query b -> Query (a, b)
join = Join ()

queryLabel :: Query' a l -> l
queryLabel (All l _) = l
queryLabel (Filter l _ _) = l
queryLabel (Sort l _ _ _ _) = l
queryLabel (Join l _ _ _) = l

deriving instance Functor (Query' a)
deriving instance Foldable (Query' a)
deriving instance Traversable (Query' a)

labelQuery :: Query a -> LQuery a
labelQuery expr = evalState (traverse (const genVar) expr) 0

substFst :: Expr (l, r) a -> l -> Expr r a
substFst (Cnst a) sub = Cnst a
substFst (Fld _ _) sub = error "Invalid field access"
substFst (Fst f) sub = Cnst (foldExpr f sub)
substFst (Snd f) sub = f
substFst (And ql qr) sub = And (substFst ql sub) (substFst qr sub)
substFst (Grt ql qr) sub = Grt (substFst ql sub) (substFst qr sub)
substFst (Plus ql qr) sub = Plus (substFst ql sub) (substFst qr sub)

tee :: Expr (Person, Person) Bool
tee = Fst ageE `Grt` Snd ageE

foldExpr :: Expr r a -> (r -> a)
foldExpr (Cnst a) = const a
foldExpr (Fld _ get) = get
foldExpr (Fst f) = \(r, _) -> foldExpr f r
foldExpr (Snd f) = \(_, r) -> foldExpr f r
foldExpr (And a b) = \r -> foldExpr a r && foldExpr b r
foldExpr (Grt a b) = \r -> foldExpr a r > foldExpr b r
foldExpr (Plus a b) = \r -> foldExpr a r + foldExpr b r

--------------------------------------------------------------------------------

data Person = Person { _name :: String, _age :: Int } deriving Show

name :: Label Person String
name = Label "name" _name

nameE :: Expr Person String
nameE = Fld "name" _name

age :: Label Person Int
age = Label "age" _age

ageE :: Expr Person Int
ageE = Fld "age" _age

expr :: Expr Person Bool
expr = (ageE `Plus` Cnst 5) `Grt` (Cnst 6)

te' :: Expr ((Person, Person), Person) Bool
te' = (Fst (Fst ageE) `Grt` (Snd ageE)) `And` (Fst (Snd ageE) `Grt` Cnst 6)

--------------------------------------------------------------------------------

aliasColumns :: String -> Ctx -> String
aliasColumns alias ctx = concat $ intersperse ", "
  [ case calias of
      Just calias' -> calias' ++ "_" ++ col ++ " as " ++ alias ++ "_" ++ calias' ++ "_" ++ col
      Nothing      -> col ++ " as " ++ alias ++ "_" ++ col
  | (calias, col) <- rootLabel ctx
  ]

foldQuerySql :: LQuery a -> (String, Ctx)
foldQuerySql (All l (Row row cols)) =
  ( "select " ++ aliasColumns l (Node [ (Nothing, col) | col <- cols ] []) ++ " from " ++ row
  , Node [ (Just l, col) | col <- cols ] []
  )
foldQuerySql (Filter l f q) =
  ( "select " ++ aliasColumns l ctx ++ " from (" ++ q' ++ ") " ++ queryLabel q ++ " where " ++ foldExprSql' ctx f
  , Node [ (Just $ maybe l (\alias -> l ++ "_" ++ alias) alias, col) | (alias, col) <- rootLabel ctx ] [ctx]
  )
  where (q', ctx) = foldQuerySql q
foldQuerySql (Join l f ql qr) =
  ( "select " ++ aliasColumns l colsl ++ ", " ++ aliasColumns l colsr ++ " from (" ++ ql' ++ ") " ++ queryLabel ql ++ " inner join (" ++ qr' ++") " ++ queryLabel qr ++ " on " ++ foldExprSql' ctx' f
  , ctx'
  )
  where (ql', colsl) = foldQuerySql ql
        (qr', colsr) = foldQuerySql qr
        ctx' = {- (\x -> trace ("\n" ++ drawTree (fmap show x) ++ "\n") x) $ -} Node [ (Just $ maybe l (\alias -> l ++ "_" ++ alias) alias, col) | (alias, col) <- rootLabel colsl ++ rootLabel colsr ]
                    [ fmap (map (\(a, c) -> (Just $ maybe l (\a -> l ++ "_" ++ a) a, c))) colsl
                    , fmap (map (\(a, c) -> (Just $ maybe l (\a -> l ++ "_" ++ a) a, c))) colsr
                    ]
                    {-
                    [ colsl
                    , colsr
                    ]
                    -}
{-
foldQuerySql (Sort l _ (Label label _) limit q) = "select * from (" ++ foldQuerySql q ++ ") " ++ queryLabel q ++ " order by " ++ queryLabel q ++ "." ++ label ++ maybe "" ((" limit " ++) . show) limit

ql = (filter (ageE `Grt` Cnst 3) $ sort name (Just 10) $ filter (ageE `Grt` Cnst 6) $ all (Row "person" ["name", "age"]))
qr = all (Row "person" ["name", "age"])
q1 = join (Fst ageE `Grt` Snd ageE) ql qr

q1sql = foldQuerySql (labelQuery q1)
-}

q2 :: Query ((Person, Person), Person)
q2 = join (Fst (Fst ageE) `Grt` Snd ageE) (join (Fst ageE `Grt` Snd ageE) allPersons allPersons) allPersons

q2sql = fst $ foldQuerySql (labelQuery q2)

allPersons = all (Row "person" ["name", "age"])

simplejoin = join (Fst ageE `Grt` Snd ageE) allPersons allPersons
simplejoinsql = fst $ foldQuerySql (labelQuery simplejoin)

simple = filter (ageE `Grt` Cnst 7) $ filter (ageE `Grt` Cnst 7) $ {- join (Fst ageE `Grt` Snd ageE) allPersons -} (filter (ageE `Grt` Cnst 6) allPersons)
simplesql = fst $ foldQuerySql (labelQuery simple)

{-

subsql = substFst (Fst age `Grt` Snd age) (Person "asd" 6)
subsqlSql = foldExprSql ("var", "fst", "snd") subsql


{-
data Limit a = forall r. Ord r => Limit (Label a r) Int | NoLimit

data Query a = Query [a] (a -> Bool) (Limit a)

-- Returns the index of the new record.
triggersQuery :: Query a -> a -> Maybe (Query a, Int)
triggersQuery (Query xs flr limit) x
  | not (flr x)              = Nothing
  | NoLimit         <- limit = Just (Query [] flr NoLimit, 0)
  | Limit (Label _ get) count <- limit
  , (pos, xs')      <- insertBy' (comparing get) x xs 0 = if pos < count
      then Just (Query (take count xs') flr limit, pos)
      else Nothing
-}

retrieveSql :: Query a -> [a]
retrieveSql = undefined

data Index a = Unknown | Index Int

fromRow :: Row -> Maybe a
fromRow = undefined

updateCache :: Ord b => QueryCache a -> Label a b -> Maybe Int -> a -> IO (Maybe (Index a))
updateCache = undefined

requestFromDb :: String -> IO [a]
requestFromDb = undefined

passesQuery :: Query a -> Row -> IO [(Index a, a)]
passesQuery (All (Row r')) row@(Row r) = if r == r'
  then case fromRow row of
    Just a -> return [(Unknown, a)]
    _      -> return []
  else return []
passesQuery (Filter f q) row = do
  rs <- passesQuery q row
  return $ filter (foldExpr f . snd) rs
passesQuery (Sort cache label limit q) row = do
  rs <- passesQuery q row
  rs' <- forM rs $ \(_, r) -> do
    index <- updateCache cache label limit r
    return ((,r) <$> index)
  return $ catMaybes rs'
passesQuery (Join f ql qr) row = do
  rl <- passesQuery ql row
  rr <- passesQuery qr row
  rs' <- forM rl $ \(_, r) -> do
    ls <- requestFromDb $ evalState (foldQuerySql $ Filter (substFst f r) qr) 0
    return [ (Unknown, (r, l)) | l <- ls ]
  return $ concat rs'

--------------------------------------------------------------------------------
-}
