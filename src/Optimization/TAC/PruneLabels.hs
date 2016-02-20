{-# LANGUAGE ViewPatterns #-}
{-|
  Module      : Optimization.TAC.PruneLabels
  Description : Replace multiple consecutive labels by one label.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Optimization.TAC.PruneLabels (
  pruneLabels
) where

import Interface.TAC (
    TAC, Command (..), Label
  )

import Prelude (
    Maybe (..),
    fst, snd, foldr, flip
  )
import Data.Functor (
    (<$>)
  )
import Data.List (
    lookup
  )

-- | Replaces multiple labels at the same instruction by only one. Additionally
--   updates the label name at all places where we would then jump to a now
--   removed label.
--
--   > label1:
--   > label2:
--   > goto label1
--
--   Might become:
--
--   > label2:
--   > goto label2
pruneLabels :: TAC -> TAC
pruneLabels tac = flip replaceRemoved removedLabels <$> newTac
  where
    replaceRemoved :: Command -> [(Label, Label)] -> Command
    replaceRemoved (Goto l) (lookup l -> Just lNew) = Goto lNew
    replaceRemoved (GotoCond1 l c d) (lookup l -> Just lNew) =
      GotoCond1 lNew c d
    replaceRemoved (GotoCond2 l c d1 d2) (lookup l -> Just lNew) =
      GotoCond2 lNew c d1 d2
    replaceRemoved c _ = c

    removedLabels :: [(Label, Label)]
    removedLabels = snd newTacAndRemovedLabels

    newTac :: TAC
    newTac = fst newTacAndRemovedLabels

    newTacAndRemovedLabels :: (TAC, [(Label, Label)])
    newTacAndRemovedLabels = foldr go ([], []) tac
      where
        go :: Command -> (TAC, [(Label, Label)]) -> (TAC, [(Label, Label)])
        go (Label l1) (Label l2 : xs, dict) = (Label l2 : xs, (l1, l2):dict)
        go x (xs, dict) = (x:xs, dict)
