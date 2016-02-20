{-|
  Module      : Optimization.TAC.UnneededLabels
  Description : Remove labels which are never jumped to.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Optimization.TAC.UnneededLabels (
  removeUnneededLabels
) where

import Interface.TAC (
    TAC, Command (..), Label,
    isGoto, getLabelFromGoto
  )

import Prelude (
    notElem, filter,
    ($)
  )
import Data.List (
    nub
  )
import Data.Functor (
    (<$>)
  )

-- * Exported functions

-- | Removes all labels from the TAC that are never jumped to by some goto
--   instruction.
removeUnneededLabels :: TAC -> TAC
removeUnneededLabels tac = removeUnneededLabels' tac
  where
    removeUnneededLabels' :: TAC -> TAC
    removeUnneededLabels' [] = []
    removeUnneededLabels' (Label l : tac_)
      | l `notElem` jumpTargets = removeUnneededLabels' tac_
    removeUnneededLabels' (t:tac_) = t : removeUnneededLabels' tac_
    -- Get all labels that are jumped to by some goto instruction
    jumpTargets :: [Label]
    jumpTargets = nub $ getLabelFromGoto <$> filter isGoto tac
