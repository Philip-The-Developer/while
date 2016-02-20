{-|
  Module      : Optimization.TAC
  Description : Performs optimizations on the intermediate code.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Optimization.TAC (
  optimize
) where

import Interface.TAC (
    TAC
  )
import Optimization.TAC.PruneLabels (
    pruneLabels
  )
import Optimization.TAC.UnnecessaryJumps (
    removeUnnecessaryJumps
  )
import Optimization.TAC.UnneededLabels (
    removeUnneededLabels
  )

import Prelude (
    (.)
  )

-- | Chain various optimization steps.
optimize :: TAC -> TAC
optimize = pruneLabels . removeUnneededLabels . removeUnnecessaryJumps
