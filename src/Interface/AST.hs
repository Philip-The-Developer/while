{-|
  Module      : Interface.AST
  Description : Defines the abstract syntax tree used in syntax analysis. This
                is already simplified from the parse tree.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
                2016, Philip Schmiel
  License     : GPL-3
-}
module Interface.AST (
  ASTPart (..),
  AST, Command (..), Expression (..), BoolExpression (..), Address (..),
  walkAST
) where

import Prelude (
    Show, Eq,
    String, Bool (..),
    show,
    (++)
  )
import qualified Prelude (
    Double, Char
  )

import Data.Int (
    Int64
  )

import Interface.Token (
    MathOp,
    RelOp,
    LogOp,
    Type
  )

-- | The type of an AST is just a command.
type AST = Command

-- | A Command consists of either of the following:
data Command
  = NONE
  | Output Expression                         -- ^ output something
  | Read Address                               -- ^ read something into a
                                              -- variable
  | Return Expression                         -- $ return something
  | Skip                                      -- ^ a no operation
  | Sequence Command Command                  -- ^ execute both commands in
                                              -- order
  | IfThen BoolExpression Command             -- ^ execute the command only if
                                              -- the expression yields true
  | IfThenElse BoolExpression Command Command -- ^ execute the first command
                                              -- on yielding true, the second
                                              -- command otherwise
  | While BoolExpression Command              -- ^ repeatedly execute the
                                              -- command as long as the
                                              -- expression yields true
  | Assign Address Expression                  -- ^ assign the value of the
                                              -- expression to an identifier
  | ArrayAlloc Type Expression Address         -- $ allocate dynamically an array
                                              -- expression to an array element
  | Declaration Type String
  | Set Address Address Expression             -- set operation
  | Environment Command                       -- $ push and pop environment
  | Function Type String Command Command          -- $ Type signature and code
  | LabelEnvironment String Command
  | Accepts Address Address                   -- set an acceptor for an object.
  deriving (Show, Eq)

-- | An arithmetic expression.
data Expression
  = Calculation MathOp Expression Expression  -- ^ Calculate with mathematical
                                              -- operator: @expr1 mathop
                                              -- expr2@
  | Negate Expression                         -- ^ Unary negation: @-expr@
  | Integer Int64                             -- $ Integer
  | Double Prelude.Double                     -- $ Double-precision floating-point number
  | Parameters Expression Expression
  | Parameter Expression
  | Character Prelude.Char                    --  Character
  | Reference String String                   --  Reference
  | Void                                      -- void value
  | ToClass String                            --  wrap a label environment to a class
  | Variable Address
  deriving (Show, Eq)

-- | A boolean expression.
data BoolExpression
  = LogOp LogOp BoolExpression BoolExpression -- ^ Calculate with logical
                                              -- operator: @bexpr1 logop
                                              -- bexpr2@
  | Comparison RelOp Expression Expression    -- ^ Compare two expressions:
                                              -- @expr1 relop expr2@
  | Not BoolExpression                        -- ^ Unary negation: @¬bexpr@
  | Boolean Bool
  | Eof                                       -- ^ End of input predicate
  deriving (Show, Eq)

data Address
  = Identifier String
  | Label String String
  | FunctionCall Address Expression
  | FromArray Address Expression
  | Structure Address Address
  deriving (Show, Eq)

data VarInfo
 = Scalar
 | Array
  deriving (Show, Eq)

-- | Walk the whole AST calling the appropriate function for each tree element.
walkAST
  :: (Command -> Command)
  -> (Expression -> Expression)
  -> (BoolExpression -> BoolExpression)
  -> AST -> AST
walkAST tc te tb = walkC
  where
    walkC :: Command -> Command
    walkC (Output e) = tc (Output (walkE e))
    walkC c@(Read _) = tc c
    walkC (Return e) = tc (Return (walkE e))                                     -- $ added
    walkC Skip = tc Skip
    walkC (Sequence c1 c2) = tc (Sequence (walkC c1) (walkC c2))
    walkC (IfThen b c) = tc (IfThen (walkB b) (walkC c))
    walkC (IfThenElse b c1 c2) = tc (IfThenElse (walkB b) (walkC c1) (walkC c2))
    walkC (While b c) = tc (While (walkB b) (walkC c))
    walkC (Assign i e) = tc (Assign i (walkE e))
    walkC (Declaration t i) = tc (Declaration t i)								 -- $ added
    walkC (ArrayAlloc t e i) = tc (ArrayAlloc t (walkE e) i)                     -- $ added
    walkC (Environment c) = tc (Environment (walkC c))                           -- $ added
    walkC (Function t id p c) = tc (Function t id (walkC p) (walkC c))         -- $ added
    walkC (LabelEnvironment i p) = tc (LabelEnvironment i (walkC p))
    walkC (NONE) = NONE
    walkC (Set addr id e) = tc (Set addr id (walkE e))
    walkC (Accepts obj hand) = tc (Accepts obj hand)

    walkE :: Expression -> Expression
    walkE (Calculation op e1 e2) = te (Calculation op (walkE e1) (walkE e2))
    walkE (Negate e) = te (Negate (walkE e))
    walkE (Parameters p1 p2) = te (Parameters (walkE p1) (walkE p2))             -- $ added
    walkE (Parameter e) = te (Parameter (walkE e))
    walkE (ToClass s) = te (ToClass s)
    walkE (Void) = te (Void)                                
    walkE e = te e

    walkB :: BoolExpression -> BoolExpression
    walkB (LogOp op b1 b2) = tb (LogOp op (walkB b1) (walkB b2))
    walkB (Comparison op e1 e2) = tb (Comparison op (walkE e1) (walkE e2))
    walkB (Not b) = tb (Not (walkB b))
    walkB b = tb b

-- | A class to output the different parts of an AST.
class ASTPart a where
  -- | Similar to 'show' but used explicitly for the AST. A string
  -- representation of the respective instance(s).
  showASTPart :: a -> String

-- | The AST command is output-able.
instance ASTPart Command where
  showASTPart (NONE) = "none"
  showASTPart (Output _) = "output"
  showASTPart (Return _) = "return"	                                          -- $ added
  showASTPart (Read _) = "read"
  showASTPart (Skip) = "skip"
  showASTPart (Sequence _ _) = ";"
  showASTPart (IfThen _ _) = "if _ then _"
  showASTPart (IfThenElse _ _ _) = "if _ then _ else _"
  showASTPart (While _ _) = "while _ do _"
  showASTPart (Assign _ _) = ":="
  showASTPart (Declaration t _) = show t ++ " _"                              -- $ added
  showASTPart (ArrayAlloc t _ _) = show t ++ "[_] _"                          -- $ added
  showASTPart (Environment _) = "push scope"                                  -- $ added
  showASTPart (Function _ _ _ _) = "function _ (_) {_}"                             -- $ added
  showASTPart (LabelEnvironment i _) = "labels "++i++"{_}"
  showASTPart (Set _ _ _) = "_ . _ <- _"
  showASTPart (Accepts _ _) = "_ accepts _"

-- | The AST expression is output-able.
instance ASTPart Expression where
  showASTPart (Calculation op _ _) = show op
  showASTPart (Negate _) = "-"
  showASTPart (Parameters _ _) = ";"         -- $ added
  showASTPart (Parameter _) = "_"
  showASTPart (Integer n) = show n           -- $ modified
  showASTPart (Double n) = show n            -- $ added
  showASTPart (Character c) = "'"++(show c)++"'"
  showASTPart (ToClass _) = "toClass _"
  showASTPart (Void) = "void"
  showASTPart (Reference _ _) = "_:_"
  showASTPart (Variable _) = "var _"

-- | The AST boolean expression is output-able.
instance ASTPart BoolExpression where
  showASTPart (LogOp op _ _) = show op
  showASTPart (Comparison op _ _) = show op
  showASTPart (Not _) = "not"
  showASTPart (Boolean True) = "true"
  showASTPart (Boolean False) = "false"
  showASTPart  Eof = "eof"
