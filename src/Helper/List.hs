{-|
  Module      : Helper.List
  Description : Helper functions for working with lists.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Helper.List (
  -- * List length functions
  atLeast, atMost, exactly
) where

import Prelude (
    Integral,
    Bool (..),
    (-), (&&)
  )

-- | Return 'True' iff the given List contains at least n Elements, where n is
--   the second argument given to the function. It does not calculate the length
--   of the list and thus also works for infinite lists.
atLeast :: Integral a => a -> [b] -> Bool
atLeast 0 _      = True
atLeast _ []     = False
atLeast n (_:ys) = atLeast (n-1) ys

-- | Return 'True' iff the given List contains at most n Elements, where n is
--   the second argument given to the function. It does not calculate the length
--   of the list and thus also works for infinite lists.
atMost :: Integral a => a -> [b] -> Bool
atMost _ []     = True
atMost 0 _      = False
atMost n (_:ys) = atMost (n-1) ys

-- | Return 'True' iff the given List contains exactly n Elements, where n is
--   the second argument given to the function. It does not calculate the length
--   of the list and thus also works for infinite lists.
exactly :: Integral a => a -> [b] -> Bool
exactly n ys = atLeast n ys && atMost n ys
