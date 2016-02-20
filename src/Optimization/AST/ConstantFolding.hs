{-|
  Module      : Optimization.AST.ConstantFolding
  Description : Performs constant folding on the AST.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
  License     : GPL-3
-}
module Optimization.AST.ConstantFolding (
  foldConstants
) where

import Prelude (
    Bool (..),
    not, error,
    (.),
    fromIntegral, rem, quot, (/)
  )

import Interface.AST (
    AST, Command (..), Expression (..), BoolExpression (..),
    walkAST
  )
import Interface.Token (
    MathOp (..), LogOp (..),
    getMathOpFunction, getRelOpFunction
  )

-- | Fold constant values.
--
--   Numerical constants which appear in calculations are replaced by the result
--   of the calculation. E.g. @x + 4 * 2@ becomes @x + 80@. Right now it only
--   calculates direct calculations things like distributivity are omitted
--   because of non algebraic behavior of computer numbers.
--
--   Boolean constants are calculated likewise. Additionally constant
--   comparisons are replaced by their boolean value and if-statements with a
--   constant condition are replaced by the corresponding command.
--
--   Skip commands are removed from the syntax tree.
foldConstants :: AST -> AST
foldConstants = walkAST commandT exprT bexprT
  where
    commandT :: Command -> Command
    commandT (Sequence Skip c) = c
    commandT (Sequence c Skip) = c
    commandT (IfThen (Boolean True) c) = c
    commandT (IfThen (Boolean False) _) = Skip
    commandT (IfThenElse (Boolean True) c _) = c
    commandT (IfThenElse (Boolean False) _ c) = c
    commandT (While (Boolean True) _) = error "You built an infinite loop"
    commandT (While (Boolean False) _) = Skip
    commandT c = c

    exprT :: Expression -> Expression
    exprT = eliminateNeutralElementAndZero . calculateNumbers

    calculateNumbers :: Expression -> Expression
    calculateNumbers (Negate (Integer n)) = Integer (-n)                         -- $ modified
    calculateNumbers (Negate (Double n)) = Double (-n)                           -- $ added
    calculateNumbers (Calculation op (Integer n1) (Double n2)) =
      calculateNumbers (Calculation op (Double (fromIntegral n1)) (Double n2))   -- $ added
    calculateNumbers (Calculation op (Double n1) (Integer n2)) =
      calculateNumbers (Calculation op (Double n1) (Double (fromIntegral n2)))   -- $ added
    calculateNumbers (Calculation Mod (Integer n1) (Integer n2)) =
      Integer (rem n1 n2)                                                        -- $ added
    calculateNumbers (Calculation DivBy (Integer n1) (Integer n2)) =
      Integer (quot n1 n2)                                                       -- $ added
    calculateNumbers (Calculation op (Integer n1) (Integer n2)) =
      Integer (getMathOpFunction op n1 n2)                                       -- $ modified
    calculateNumbers (Calculation Mod (Double _) (Double _)) =
      error "Modulo only applicable to Integers"                                 -- $ added
    calculateNumbers (Calculation DivBy (Double n1) (Double n2)) =
      Double ((/) n1 n2)                                                         -- $ added
    calculateNumbers (Calculation op (Double n1) (Double n2)) =
      Double (getMathOpFunction op n1 n2)                                        -- $ added
    calculateNumbers e = e

    eliminateNeutralElementAndZero :: Expression -> Expression
    eliminateNeutralElementAndZero (Calculation Plus (Integer 0) x) = x          -- $ modified
    eliminateNeutralElementAndZero (Calculation Plus x (Integer 0)) = x          -- $ modified
    eliminateNeutralElementAndZero (Calculation Minus (Integer 0) x) = Negate x  -- $ modified
    eliminateNeutralElementAndZero (Calculation Minus x (Integer 0)) = x         -- $ modified
    eliminateNeutralElementAndZero (Calculation Times (Integer 1) x) = x         -- $ modified
    eliminateNeutralElementAndZero (Calculation Times x (Integer 1)) = x         -- $ modified
    eliminateNeutralElementAndZero (Calculation Times (Integer 0) _) = Integer 0 -- $ modified
    eliminateNeutralElementAndZero (Calculation Times _ (Integer 0)) = Integer 0 -- $ modified
    eliminateNeutralElementAndZero (Calculation DivBy x (Integer 1)) = x         -- $ modified
    eliminateNeutralElementAndZero (Calculation DivBy _ (Integer 0)) =           -- $ modified
      error "Division by constant zero detected"
    eliminateNeutralElementAndZero (Calculation DivBy (Integer 0) _) = Integer 0 -- $ modified
	
    eliminateNeutralElementAndZero (Calculation Plus (Double 0) x) = x           -- $ added
    eliminateNeutralElementAndZero (Calculation Plus x (Double 0)) = x           -- $ added
    eliminateNeutralElementAndZero (Calculation Minus (Double 0) x) = Negate x   -- $ added
    eliminateNeutralElementAndZero (Calculation Minus x (Double 0)) = x          -- $ added
    eliminateNeutralElementAndZero (Calculation Times (Double 1) x) = x          -- $ added
    eliminateNeutralElementAndZero (Calculation Times x (Double 1)) = x          -- $ added
    eliminateNeutralElementAndZero (Calculation Times (Double 0) _) = Integer 0  -- $ added
    eliminateNeutralElementAndZero (Calculation Times _ (Double 0)) = Integer 0  -- $ added
    eliminateNeutralElementAndZero (Calculation DivBy x (Double 1)) = x          -- $ added
    eliminateNeutralElementAndZero (Calculation DivBy _ (Double 0)) =            -- $ added
      error "Division by constant zero detected"
    eliminateNeutralElementAndZero (Calculation DivBy (Double 0) _) = Integer 0  -- $ added
    eliminateNeutralElementAndZero e = e

    bexprT :: BoolExpression -> BoolExpression
    bexprT (Not (Boolean b)) = Boolean (not b)
    bexprT (Not (Not be)) = be

    bexprT (LogOp And (Boolean True) be) = be
    bexprT (LogOp And be (Boolean True)) = be
    bexprT (LogOp And be@(Boolean False) _) = be
    bexprT (LogOp And _ be@(Boolean False)) = be

    bexprT (LogOp Or (Boolean False) be) = be
    bexprT (LogOp Or be (Boolean False)) = be
    bexprT (LogOp Or be@(Boolean True) _) = be
    bexprT (LogOp Or _ be@(Boolean True)) = be

    bexprT (Comparison op (Integer n1) (Double n2)) =    -- $ modified
      Boolean (getRelOpFunction op (fromIntegral n1) n2)
    bexprT (Comparison op (Double n1) (Integer n2)) =    -- $ modified
      Boolean (getRelOpFunction op n1 (fromIntegral n2))
    bexprT (Comparison op (Integer n1) (Integer n2)) =   -- $ modified
      Boolean (getRelOpFunction op n1 n2)
    bexprT (Comparison op (Double n1) (Double n2)) =     -- $ modified
      Boolean (getRelOpFunction op n1 n2)

    bexprT be = be
