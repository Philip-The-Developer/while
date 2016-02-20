{-|
  Module      : Optimization.TAC.UnnecessaryJumps
  Description : Remove unnecessary jump instructions.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Optimization.TAC.UnnecessaryJumps (
  removeUnnecessaryJumps
) where

import Interface.TAC (
    TAC, Command (..),
    invertCond1, invertCond2
  )

import Prelude (
    (==)
  )

-- | Replaces a conditional jump to label /x/ followed by an unconditional jump
--   to label /y/ followed by label /x/ with just one conditional jump to label
--   /y/. Thus
--
--   > goto label6 if i <= num
--   > goto label2
--   > label6:
--
--   becomes
--
--   > goto label2 if i > num
removeUnnecessaryJumps :: TAC -> TAC
removeUnnecessaryJumps [] = []

removeUnnecessaryJumps (GotoCond1 l1 c d : Goto l2 : Label l3 : tac)
  | l1 == l3 = GotoCond1 l2 (invertCond1 c) d : Label l3
             : removeUnnecessaryJumps tac
removeUnnecessaryJumps (GotoCond2 l1 c d1 d2 : Goto l2 : Label l3 : tac)
  | l1 == l3 = GotoCond2 l2 (invertCond2 c) d1 d2 : Label l3
             : removeUnnecessaryJumps tac
-- Remove every goto instruction that jumps to a directly following label
removeUnnecessaryJumps (Goto l1 : Label l2 : tac)
  | l1 == l2 = Label l2 : removeUnnecessaryJumps tac

removeUnnecessaryJumps (t:tac) = t : removeUnnecessaryJumps tac
