module Database.Value.PSet where

import Database.Value.VTM

data PSet a = PSet String [a -> IO ()]

newPSet :: VTM (PSet a)
newPSet = undefined
