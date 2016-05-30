{-|
  Module      : Interface.Token
  Description : Defines token types used by multiple modules.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
                2016, Philip Schmiel
  License     : GPL-3
-}
module Interface.Token (
  PosToken (..), Token (..), LogOp (..), RelOp (..), MathOp (..), Type (..),
  getPosition, removePosition, removePositions, getMathOpFunction,
  getRelOpFunction
) where

import Prelude (
    String, Bool,
    Show, Eq, Integral, Num, Ord,
    (++), (==), (/=), (<), (<=), (>), (>=), (+), (-), (*),
    show, fmap, quot, rem
  )
import qualified Prelude (
    Double, Char
  )

import Data.Int (
    Int64
  )

import Interface.Pos (
    SourcePos
  )

-- | A data type for tokens generated during the lexing phase which have a
-- position inside the source code attached.
data PosToken
  = PosToken {
    position :: SourcePos,  -- ^ The position of the token
    token :: Token          -- ^ The token itself
  }

-- | Display positioned tokens like tokens and add position information at the
-- end.
instance Show PosToken where
  show pt = show (token pt) ++ "@" ++ show (position pt)

-- | Ignore the token position when looking for equality.
instance Eq PosToken where
  pt1 == pt2 = token pt1 == token pt2

-- | A data type for the tokens generated during the lexing phase.
data Token
  = Id String              -- ^ All possible variable names (@stuff@, @foo@, @bar@, …)
  | DInt Int64          -- $ Integer number (@34@, @132@, @894@, …)
  | DDouble Prelude.Double    -- $ Double-precision floating-point number (@34.1@, @132.1@, @894.1@, …)
  | DBool Bool           -- ^ Boolean values (@true@ and @false@)
  | DChar Prelude.Char --   Character (@'a'@, @'b'@, @'c'@)
  | LogOp LogOp            -- ^ Logical operators (@and@ and @or@)
  | Not                    -- ^ Boolean negation (@not@)
  | RelOp RelOp            -- ^ Relational operators (@=@, @<@, @<=@, @>@, @>=@ and @!=@)
  | MathOp MathOp          -- ^ Arithmetic operators (@mod@, @+@, @-@, @*@, @/@)
  | Assign                 -- ^ The assignment operator (@:=@)
  | Eof                    -- ^ The eof predicate (@eof@)
  | Read                   -- ^ The read token (@read@)
  | Output                 -- ^ The output token (@output@)
  | Return                 -- $ The return token (@return@)
  | If                     -- ^ If
  | Then                   -- ^ Then
  | Else                   -- ^ Else
  | While                  -- ^ While
  | Do                     -- ^ Do
  | Function               -- $ Function
  | Token Prelude.Char             -- ^ Single char tokens – used for parentheses, braces, …
  | Type Type              -- $ Base types (@int@ and @float@)  
  deriving (Eq)

-- | Display tokens in the form @\<token[,attribute]\>@.
instance Show Token where
  show (Id i)         = "<id,\"" ++ i ++ "\">"
  show (DInt n)       = "<integer," ++ show n ++ ">"  -- $ modified
  show (DDouble n)    = "<real," ++ show n ++ ">"     -- $ added
  show (DBool b)      = "<boolean," ++ show b ++ ">"
  show (DChar c)      = "character," ++ show c ++ ">"
  show (LogOp lo)     = "<logop," ++ show lo ++ ">"
  show Not            = "<not>"
  show (RelOp ro)     = "<relop," ++ show ro ++ ">"
  show (MathOp mo)    = "<mathop," ++ show mo ++ ">"
  show Assign         = "<:=>"
  show Eof            = "<eof>"
  show Read           = "<read>"
  show Output         = "<output>"
  show Return         = "<return>"                    -- $ added
  show If             = "<if>"
  show Then           = "<then>"
  show Else           = "<else>"
  show While          = "<while>"
  show Do             = "<do>"
  show (Type t)       = "<type,\"" ++ show t ++ "\">" -- $ added
  show Function       = "<function>"                  -- $ added
  show (Token c)      = "<" ++ [c] ++ ">"

-- | Operations on boolean values.
data LogOp
  = And  -- ^ Boolean and (@and@)
  | Or   -- ^ Boolean or (@or@)
  deriving (Eq)

-- | Display as @and@ or @or@.
instance Show LogOp where
  show And = "and"
  show Or  = "or"

-- | Relational operations to compare numbers.
data RelOp
  = Eq   -- ^ Equals (@=@)
  | Neq  -- ^ Not equals (@!=@)
  | Lt   -- ^ Less than (@<@)
  | Lte  -- ^ Less than or equal (@<=@)
  | Gt   -- ^ Greater than (@>@)
  | Gte  -- ^ Greater than or equal (@>=@)
  deriving (Eq)

-- | Display symbolic names as their respective symbols.
instance Show RelOp where
  show Eq  = "="
  show Neq = "!="
  show Lt  = "<"
  show Lte = "<="
  show Gt  = ">"
  show Gte = ">="

-- | Mathematical operations for numbers.
data MathOp
  = Mod      -- ^ Modulo operation (@mod@)
  | Plus     -- ^ The plus sign (@+@)
  | Minus    -- ^ The minus sign (@-@)
  | Times    -- ^ The times star (@*@)
  | DivBy    -- ^ The division slash (@/@)
  deriving (Eq)

-- | Display symbolic names as their respective symbols.
instance Show MathOp where
  show Mod   = "mod"
  show Plus  = "+"
  show Minus = "-"
  show Times = "*"
  show DivBy = "/"

-- $| Basic type declarations.
data Type
  = TInt         -- $ Integer declaration (@int@)
  | TDouble      -- $ Double-precision floating-point number declaration (@double@)
  | TChar        --   Character declaration (@char@)
  deriving (Eq)

-- $| Display as @int@ or @double@.
instance Show Type where
  show TInt    = "int"
  show TDouble = "double"
  show TChar   = "char"

-- | Gets the position from a token.
getPosition :: PosToken -> SourcePos
getPosition = position

-- | "Removes" the position from a token.
removePosition :: PosToken -> Token
removePosition = token

-- | "Removes" the position from a list of tokens.
removePositions :: [PosToken] -> [Token]
removePositions = fmap removePosition

-- | Returns the function represented by a mathematical operator token.
getMathOpFunction :: (Num a) => MathOp -> a -> a -> a -- $ modified
getMathOpFunction Plus = (+)
getMathOpFunction Minus = (-)
getMathOpFunction Times = (*)

-- | Returns the function represented by a logical operator token.
getRelOpFunction :: (Ord a) => RelOp -> a -> a -> Bool
getRelOpFunction Eq = (==)
getRelOpFunction Neq = (/=)
getRelOpFunction Lt = (<)
getRelOpFunction Lte = (<=)
getRelOpFunction Gt = (>)
getRelOpFunction Gte = (>=)
