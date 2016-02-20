{-|
  Module      : Interface.AST
  Description : Defines the abstract syntax tree used in syntax analysis. This
                is already simplified from the parse tree.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
  License     : GPL-3
-}
module Interface.AST (
  ASTPart (..),
  AST, Command (..), Expression (..), BoolExpression (..),
  walkAST
) where

import Prelude (
    Show, Eq,
    String, Bool (..),
    show,
    (++)
  )
import qualified Prelude (
    Double
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
  = Output Expression                         -- ^ output something
  | Read String                               -- ^ read something into a
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
  | Assign String Expression                  -- ^ assign the value of the
                                              -- expression to an identifier
  | Declaration Type String                   -- $ declare type of a variable
  | ArrayDecl Type String                     -- $ declare an array
  | ArrayAlloc Type Expression String         -- $ allocate dynamically an array
  | ToArray String Expression Expression      -- $ assign the value of the
                                              -- expression to an array element
  | Environment Command                       -- $ push and pop environment
  | Function Command Command Command          -- $ Type signature and code
  deriving (Show, Eq)

-- | An arithmetic expression.
data Expression
  = Calculation MathOp Expression Expression  -- ^ Calculate with mathematical
                                              -- operator: @expr1 mathop
                                              -- expr2@
  | Negate Expression                         -- ^ Unary negation: @-expr@
  | Identifier String                         -- ^ Variable: @a@, @b@, …
  | FromArray String Expression               -- $ Array element: @a[0]@, @b[i]@, …
  | Parameter Expression                      -- $ Parameter: @a@, 0+1, …
  | Parameters Expression Expression          -- $ Series of parameters
  | Func String Expression                    -- $ Function call: @f(a; b; c)@, @g(x; y; z)@, …
  | Integer Int64                             -- $ Integer
  | Double Prelude.Double                     -- $ Double-precision floating-point number
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
    walkC (ArrayDecl t i) = tc (ArrayDecl t i)                                   -- $ added
    walkC (ArrayAlloc t e i) = tc (ArrayAlloc t (walkE e) i)                     -- $ added
    walkC (ToArray i e1 e2) = tc (ToArray i (walkE e1) (walkE e2))               -- $ added
    walkC (Environment c) = tc (Environment (walkC c))                           -- $ added
    walkC (Function t p c) = tc (Function (walkC t) (walkC p) (walkC c))         -- $ added

    walkE :: Expression -> Expression
    walkE (Calculation op e1 e2) = te (Calculation op (walkE e1) (walkE e2))
    walkE (Negate e) = te (Negate (walkE e))
    walkE (FromArray i e) = te (FromArray i (walkE e))                           -- $ added
    walkE (Parameter p) = te (Parameter (walkE p))                               -- $ added
    walkE (Parameters p1 p2) = te (Parameters (walkE p1) (walkE p2))             -- $ added
    walkE (Func f p) = te (Func f (walkE p))                                     -- $ added
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
  showASTPart (Output _) = "output"
  showASTPart (Return _) = "return"	                                          -- $ added
  showASTPart (Read _) = "read"
  showASTPart (Skip) = "skip"
  showASTPart (Sequence _ _) = ";"
  showASTPart (IfThen _ _) = "if _ then _"
  showASTPart (IfThenElse _ _ _) = "if _ then _ else _"
  showASTPart (While _ _) = "while _ do _"
  showASTPart (Assign _ _) = ":="
  showASTPart (ToArray _ _ _) = ":="                                          -- $ added
  showASTPart (Declaration t _) = show t ++ " _"                              -- $ added
  showASTPart (ArrayDecl t _) = show t ++ "[] _"                              -- $ added
  showASTPart (ArrayAlloc t _ _) = show t ++ "[_] _"                          -- $ added
  showASTPart (Environment _) = "push scope"                                  -- $ added
  showASTPart (Function _ _ _) = "function _ (_) {_}"                             -- $ added

-- | The AST expression is output-able.
instance ASTPart Expression where
  showASTPart (Calculation op _ _) = show op
  showASTPart (Negate _) = "-"
  showASTPart (Identifier i) = i
  showASTPart (FromArray i _) = "_[_]"       -- $ added
  showASTPart (Parameter p) = showASTPart p  -- $ added
  showASTPart (Parameters _ _) = ";"         -- $ added
  showASTPart (Func _ _) = "_(_)"            -- $ added
  showASTPart (Integer n) = show n           -- $ modified
  showASTPart (Double n) = show n            -- $ added

-- | The AST boolean expression is output-able.
instance ASTPart BoolExpression where
  showASTPart (LogOp op _ _) = show op
  showASTPart (Comparison op _ _) = show op
  showASTPart (Not _) = "not"
  showASTPart (Boolean True) = "true"
  showASTPart (Boolean False) = "false"
  showASTPart  Eof = "eof"
