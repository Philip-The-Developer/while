{-|
  Module      : Interface.TAC
  Description : Defines the three address code which is generated from the
                syntax tree.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
                2016, Philip Schmiel
  License     : GPL-3
-}
module Interface.TAC (
  TAC, Command (..), Data (..), Variable, ImmediateInteger, ImmediateDouble, ImmediateChar, Label, GotoCondition1 (..),
  GotoCondition2 (..),
  invertCond1, invertCond2, isGoto, getLabelFromGoto,
  getDefVariables, getUseVariables, getVariables, renameVariables
) where

import Prelude (
    Show (show), Eq, Char,
    String, Bool (..),
    error,
    (++), ($), (==),
    Double
  )

import Data.Int (
    Int64
  )

-- | A three address code is a list of three address code commands
type TAC = [Command]

-- | The three address code commands are low level instructions (similar to
-- machine instruction).
data Command
  = Read Variable
  | Output Data
  | FRead Variable          -- $ added
  | FOutput Data            -- $ added
  | CRead Variable
  | COutput Data
  | Return Data             -- $ added
  | FReturn Data            -- $ added
  | Pop Variable            -- $ added
  | Push Data               -- $ added
  | ArrayAlloc Variable Data-- $ added
  | ArrayDealloc Variable   -- $ added
  | FromArray Variable Variable Data-- $ added
  | ToArray Variable Data Data-- $ added
  | ArrayCopy Variable Data -- $ added
  | Copy Variable Data
  | Convert Variable Data   -- $ added
  | ConvertInt Variable Data
  | Add Variable Data Data
  | Sub Variable Data Data
  | Mul Variable Data Data
  | Div Variable Data Data
  | Mod Variable Data Data
  | Neg Variable Data
  | Call Variable Label     -- $ added
  | FAdd Variable Data Data -- $ added
  | FSub Variable Data Data -- $ added
  | FMul Variable Data Data -- $ added
  | FDiv Variable Data Data -- $ added
  | FNeg Variable Data      -- $ added
  | Goto Label
  | GotoCond1 Label GotoCondition1 Data
  | GotoCond2 Label GotoCondition2 Data Data
  | Label Label
  deriving (Eq)

-- | Gives a neat output for three address commands.
instance Show Command where
  show (Read v) = "read " ++ v
  show (Output d) = "output " ++ show d
  show (FRead v) = "read " ++ v                                   -- $ added
  show (FOutput d) = "output " ++ show d                          -- $ added
  show (CRead v) = "read " ++ v
  show (COutput d) = "output " ++ show d
  show (Return d) = "return " ++ show d                           -- $ added
  show (FReturn d) = "return " ++ show d                          -- $ added
  show (Pop v) = "pop " ++ v                                      -- $ added
  show (Push d) = "push " ++ show d                               -- $ added
  show (ArrayAlloc v _) = "alloc " ++ v                           -- $ added
  show (ArrayDealloc v) = "dealloc " ++ v                         -- $ added
  show (FromArray v1 v2 d) = v1++" = "++v2++"["++show d++"]"      -- $ added
  show (ToArray v d1 d2) = v ++ "[" ++ show d1 ++ "] = " ++ show d2-- $ added
  show (ArrayCopy v d) = if v == show d then ""
                                        else v ++ " = " ++ show d -- $ added
  show (Copy v d) = v ++ " = " ++ show d
  show (Convert v d) = v ++ " = (double)" ++ show d               -- $ added
  show (ConvertInt v d) = v ++ " = (int)" ++ show d
  show (Add v d1 d2) = v ++ " = " ++ show d1 ++ " + " ++ show d2
  show (Sub v d1 d2) = v ++ " = " ++ show d1 ++ " - " ++ show d2
  show (Mul v d1 d2) = v ++ " = " ++ show d1 ++ " * " ++ show d2
  show (Div v d1 d2) = v ++ " = " ++ show d1 ++ " / " ++ show d2
  show (Mod v d1 d2) = v ++ " = " ++ show d1 ++ " % " ++ show d2
  show (Neg v d) = v ++ " = -" ++ show d
  show (Call v l) = v ++ " = " ++ l                               -- $ added
  show (FAdd v d1 d2) = v ++ " = " ++ show d1 ++ " + " ++ show d2 -- $ added
  show (FSub v d1 d2) = v ++ " = " ++ show d1 ++ " - " ++ show d2 -- $ added
  show (FMul v d1 d2) = v ++ " = " ++ show d1 ++ " * " ++ show d2 -- $ added
  show (FDiv v d1 d2) = v ++ " = " ++ show d1 ++ " / " ++ show d2 -- $ added
  show (FNeg v d) = v ++ " = -" ++ show d                         -- $ added
  show (Goto l) = "goto " ++ l
  show (GotoCond1 l cond d) = "goto " ++ l ++ " if " ++ show cond ++ " " ++
                              show d
  show (GotoCond2 l cond d1 d2) = "goto " ++ l ++ " if " ++ show d1 ++ " " ++
                                  show cond ++ " " ++ show d2
  show (Label l) = l ++ ":"

-- | The different conditions for a goto statement with one parameter.
data GotoCondition1
  = IsTrue  -- ^ The parameter (a boolean value) should be true
  | IsFalse -- ^ The parameter (a boolean value) should be false
  deriving (Eq)

-- | Show nothing for 'IsTrue' and @not@ for 'IsFalse'.
instance Show GotoCondition1 where
  show IsTrue = ""
  show IsFalse = "not"

-- | Invert the one-parameter-condition (effectively swapping true and false).
invertCond1 :: GotoCondition1 -> GotoCondition1
invertCond1 IsTrue = IsFalse
invertCond1 IsFalse = IsTrue

-- | The different conditions for a goto statement with two parameters, i.e.
--   jumps with a comparison operator.
data GotoCondition2
  = Equal
  | NotEqual
  | Greater
  | GreaterEqual
  | Less
  | LessEqual
  | FEqual         -- $ added
  | FNotEqual      -- $ added
  | FGreater       -- $ added
  | FGreaterEqual  -- $ added
  | FLess          -- $ added
  | FLessEqual     -- $ added
  deriving (Eq)

-- | Display the symbol which belongs to the condition.
instance Show GotoCondition2 where
  show Equal = "=="
  show NotEqual = "!="
  show Greater = ">"
  show GreaterEqual = ">="
  show Less = "<"
  show LessEqual = "<="
  show FEqual = "=="        -- $ added
  show FNotEqual = "!="     -- $ added
  show FGreater = ">"       -- $ added
  show FGreaterEqual = ">=" -- $ added
  show FLess = "<"          -- $ added
  show FLessEqual = "<="    -- $ added

-- | Invert the two-parameter-condition (@Equal@ ⇔ @NotEqual@, @Greater@ ⇔
--   @LessEqual@, @GreaterEqual@ ⇔ @Less@).
invertCond2 :: GotoCondition2 -> GotoCondition2
invertCond2 Equal = NotEqual
invertCond2 NotEqual = Equal
invertCond2 Greater = LessEqual
invertCond2 GreaterEqual = Less
invertCond2 Less = GreaterEqual
invertCond2 LessEqual = Greater
invertCond2 FEqual = FNotEqual    -- $ added
invertCond2 FNotEqual = FEqual    -- $ added
invertCond2 FGreater = FLessEqual -- $ added
invertCond2 FGreaterEqual = FLess -- $ added
invertCond2 FLess = FGreaterEqual -- $ added
invertCond2 FLessEqual = FGreater -- $ added

-- | Three address codes can work on general data, i.e. they don't care whether
-- they work on variables or immediate values.
data Data
  = Variable Variable
  | ImmediateInteger ImmediateInteger -- $ modified
  | ImmediateDouble ImmediateDouble   -- $ added
  | ImmediateChar ImmediateChar
  deriving (Eq)

-- | Returns variable names as they are and applies `show` to immediate values.
instance Show Data where
  show (Variable v) = v
  show (ImmediateInteger i) = show i                             -- $ modified
  show (ImmediateDouble i) = show i                              -- $ added
  show (ImmediateChar c) = show c                              

-- | Variable names are just strings.
type Variable = String

-- $| Integers as values.
type ImmediateInteger = Int64

-- $| Double-precision floating-point numbers as values.
type ImmediateDouble = Double

-- |Character as values
type ImmediateChar = Char

-- | Labels are just names, i.e. strings.
type Label = String

-- * Helper functions

-- | Check whether a command is a goto instruction.
isGoto :: Command -> Bool
isGoto (Goto _)            = True
isGoto (GotoCond1 _ _ _)   = True
isGoto (GotoCond2 _ _ _ _) = True
isGoto _                   = False

-- | Retrieve the target label from a goto instruction.
getLabelFromGoto :: Command -> Label
getLabelFromGoto (Goto l)            = l
getLabelFromGoto (GotoCond1 l _ _)   = l
getLabelFromGoto (GotoCond2 l _ _ _) = l
getLabelFromGoto c = error $ "Cannot get label from " ++ show c


getDefVariables :: Command -> [Variable]
getDefVariables (Read v) = [v]
getDefVariables (FRead v) = [v]        -- $ added
getDefVariables (CRead v) = [v]
getDefVariables (Pop v) = [v]          -- $ added
getDefVariables (ArrayAlloc v _) = [v] -- $ added
getDefVariables (FromArray v _ _) = [v]-- $ added
getDefVariables (ArrayCopy v _) = [v]  -- $ added
getDefVariables (Copy v _) = [v]
getDefVariables (Convert v _) = [v]    -- $ added
getDefVariables (ConvertInt v _ ) = [v]
getDefVariables (Add v _ _) = [v]
getDefVariables (Sub v _ _) = [v]
getDefVariables (Mul v _ _) = [v]
getDefVariables (Div v _ _) = [v]
getDefVariables (Mod v _ _) = [v]
getDefVariables (Neg v _) = [v]
getDefVariables (Call v _) = [v]       -- $ added
getDefVariables (FAdd v _ _) = [v]     -- $ added
getDefVariables (FSub v _ _) = [v]     -- $ added
getDefVariables (FMul v _ _) = [v]     -- $ added
getDefVariables (FDiv v _ _) = [v]     -- $ added
getDefVariables (FNeg v _) = [v]       -- $ added
getDefVariables _ = []

getUseVariables :: Command -> [Variable]
getUseVariables (Output (Variable v)) = [v]
getUseVariables (Return (Variable v)) = [v]               -- $ added
getUseVariables (FReturn (Variable v)) = [v]              -- $ added
getUseVariables (FOutput (Variable v)) = [v]                -- $ added
getUseVariables (COutput (Variable v)) = [v]
getUseVariables (Push (Variable v)) = [v]                   -- $ added
getUseVariables (ArrayAlloc _ d1) = variablesFromData [d1]  -- $ added
getUseVariables (ArrayDealloc v) = [v]                     -- $ added
getUseVariables (FromArray _ v2 d1) = [v2] ++ variablesFromData [d1] -- $ added
getUseVariables (ToArray v d1 d2) = [v] ++ variablesFromData [d1, d2] -- $ added
getUseVariables (ArrayCopy _ d1) = variablesFromData [d1]   -- $ added
getUseVariables (Copy _ d1) = variablesFromData [d1]
getUseVariables (Convert _ d1) = variablesFromData [d1]     -- $ added
getUseVariables (ConvertInt _ d1) = variablesFromData [d1]
getUseVariables (Add _ d1 d2) = variablesFromData [d1, d2]
getUseVariables (Sub _ d1 d2) = variablesFromData [d1, d2]
getUseVariables (Mul _ d1 d2) = variablesFromData [d1, d2]
getUseVariables (Div _ d1 d2) = variablesFromData [d1, d2]
getUseVariables (Mod _ d1 d2) = variablesFromData [d1, d2]
getUseVariables (Neg _ d1) = variablesFromData [d1]
getUseVariables (FAdd _ d1 d2) = variablesFromData [d1, d2] -- $ added
getUseVariables (FSub _ d1 d2) = variablesFromData [d1, d2] -- $ added
getUseVariables (FMul _ d1 d2) = variablesFromData [d1, d2] -- $ added
getUseVariables (FDiv _ d1 d2) = variablesFromData [d1, d2] -- $ added
getUseVariables (FNeg _ d1) = variablesFromData [d1]        -- $ added
getUseVariables (GotoCond1 _ _ d1) = variablesFromData [d1]
getUseVariables (GotoCond2 _ _ d1 d2) = variablesFromData [d1, d2]
getUseVariables _ = []

getVariables :: Command -> [Variable]
getVariables c = getDefVariables c ++ getUseVariables c

renameVariables :: Command -> Variable -> Variable -> Command
renameVariables (Output d) vI vO =
  let [d'] = substitute [d] vI vO
  in Output d'
renameVariables (FOutput d) vI vO =                                   -- $ added
  let [d'] = substitute [d] vI vO
  in FOutput d'
renameVariables (COutput d) vI vO =
  let [d'] = substitute [d] vI vO
  in COutput d'
renameVariables (Return d) vI vO =                                    -- $ added
  let [d'] = substitute [d] vI vO
  in Return d'
renameVariables (FReturn d) vI vO =                                   -- $ added
  let [d'] = substitute [d] vI vO
  in FReturn d'
renameVariables (Read v) vI vO =
  let [Variable v'] = substitute [Variable v] vI vO
  in Read v'
renameVariables (FRead v) vI vO =                                     -- $ added
  let [Variable v'] = substitute [Variable v] vI vO
  in FRead v'
renameVariables (CRead v) vI vO =
  let [Variable v'] = substitute [Variable v] vI vO
  in CRead v'
renameVariables (Push d) vI vO =                                      -- $ added
  let [d'] = substitute [d] vI vO
  in Push d'
renameVariables (Pop v) vI vO =                                       -- $ added
  let [Variable v'] = substitute [Variable v] vI vO
  in Pop v'
renameVariables (ArrayAlloc v d) vI vO =                              -- $ added
  let [Variable v', d'] = substitute [Variable v, d] vI vO
  in ArrayAlloc v' d'
renameVariables (ArrayDealloc v) vI vO =                              -- $ added
  let [Variable v'] = substitute [Variable v] vI vO
  in ArrayDealloc v'
renameVariables (FromArray v1 v2 d) vI vO =                           -- $ added
  let [Variable v1', Variable v2', d'] = substitute [Variable v1, Variable v2, d] vI vO
  in FromArray v1' v2' d'
renameVariables (ToArray v d1 d2) vI vO =                             -- $ added
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in ToArray v' d1' d2'
renameVariables (ArrayCopy v d) vI vO =                               -- $ added
  let [Variable v', d'] = substitute [Variable v, d] vI vO
  in ArrayCopy v' d'
renameVariables (Copy v d) vI vO =
  let [Variable v', d'] = substitute [Variable v, d] vI vO
  in Copy v' d'
renameVariables (Convert v d) vI vO =                                 -- $ added
  let [Variable v', d'] = substitute [Variable v, d] vI vO
  in Convert v' d'
renameVariables (ConvertInt v d) vI vO =
  let [Variable v', d'] = substitute [Variable v, d] vI vO
  in ConvertInt v' d'
renameVariables (Add v d1 d2) vI vO =
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in Add v' d1' d2'
renameVariables (Sub v d1 d2) vI vO =
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in Sub v' d1' d2'
renameVariables (Mul v d1 d2) vI vO =
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in Mul v' d1' d2'
renameVariables (Div v d1 d2) vI vO =
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in Div v' d1' d2'
renameVariables (Mod v d1 d2) vI vO =
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in Mod v' d1' d2'
renameVariables (Neg v d) vI vO =
  let [Variable v', d'] = substitute [Variable v, d] vI vO
  in Neg v' d'
renameVariables (Call v l) vI vO =                                    -- $ added
  let [Variable v'] = substitute [Variable v] vI vO
  in Call v' l
renameVariables (FAdd v d1 d2) vI vO =                                -- $ added
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in FAdd v' d1' d2'
renameVariables (FSub v d1 d2) vI vO =                                -- $ added
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in FSub v' d1' d2'
renameVariables (FMul v d1 d2) vI vO =                                -- $ added
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in FMul v' d1' d2'
renameVariables (FDiv v d1 d2) vI vO =                                -- $ added
  let [Variable v', d1', d2'] = substitute [Variable v, d1, d2] vI vO
  in FDiv v' d1' d2'
renameVariables (FNeg v d) vI vO =                                    -- $ added
  let [Variable v', d'] = substitute [Variable v, d] vI vO
  in FNeg v' d'
renameVariables (GotoCond1 l c d) vI vO =
  let [d'] = substitute [d] vI vO
  in GotoCond1 l c d'
renameVariables (GotoCond2 l c d1 d2) vI vO =
  let [d1', d2'] = substitute [d1, d2] vI vO
  in GotoCond2 l c d1' d2'
renameVariables c _ _ = c

substitute :: [Data] -> Variable -> Variable -> [Data]
substitute [] _ _ = []
substitute (Variable v : rest) vIn vOut
  | v == vIn = Variable vOut : substitute rest vIn vOut
substitute (d:rest) vIn vOut = d : substitute rest vIn vOut

variablesFromData :: [Data] -> [Variable]
variablesFromData [] = []
variablesFromData (Variable v : data_) = v : variablesFromData data_
variablesFromData (_ : data_) = variablesFromData data_
