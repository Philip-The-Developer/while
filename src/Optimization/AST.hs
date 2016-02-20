{-|
  Module      : Optimization.AST
  Description : Performs optimizations on the AST.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Optimization.AST (
  optimize
) where

import Interface.AST (
    AST
  )
import Optimization.AST.ConstantFolding (
    foldConstants
  )

-- | Chain various optimization steps.
optimize :: AST -> AST
optimize = foldConstants
