{-|
  Module      : Helper.Tuple
  Description : Helper functions for working with lists.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Helper.Tuple (
  -- * Triple functions
  first, second, third
) where

-- | Return the first element from a three-tuple.
first :: (a, b, c) -> a
first (x, _, _) = x

-- | Return the second element from a three-tuple.
second :: (a, b, c) -> b
second (_, x, _) = x

-- | Return the third element from a three-tuple.
third :: (a, b, c) -> c
third (_, _, x) = x
