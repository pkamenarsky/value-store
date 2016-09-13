{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Database.Bookkeeper where

import Bookkeeper
import Bookkeeper.Internal

import Database.Generic

instance Fields (Book' kvs) where
  fields = undefined
  cnst = undefined
  cnstM = undefined
  cnstS = undefined
