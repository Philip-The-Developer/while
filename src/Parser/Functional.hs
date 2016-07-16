{-# OPTIONS_HADDOCK ignore-exports #-}
{-|
  Module      : Parser.Functional
  Description : Parses a token stream into an abstract syntax tree in a
                functional way.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
  License     : GPL-3
-}
module Parser.Functional (
  parse
) where

import Parser.Functional.Library (
    Parser (..),
    next, eof, chainl1, mzero,
    (<|>)
  )
import Interface.Token (
    PosToken, Token (..), RelOp, MathOp (..), LogOp (..),
    removePosition,
    Type
  )
import Interface.AST (
    AST
  )
import qualified Interface.AST as A (
    Command (..), Expression (..), BoolExpression (..)
  )

import Prelude (
    Monad (..),
    Bool (..), String, Maybe (..),
    error,
    (==), ($),
    Double
  )
import Data.Int (
    Int64
  )

-- * Exported functions

-- | Parse a token stream into an abstract syntax tree.
parse :: [PosToken] -> AST
parse input = case runParser program input of
                Just (ast, _) -> ast
                _             -> error "Functional parser: error parsing input."

-- * WHILE-Parser

-- | A parser with the stream type of @['PosToken']@.
type TokenParser = Parser [PosToken]

-- ** Non-terminal parsers

program :: TokenParser A.Command
program = do
  c <- cmds
  eof
  return c

cmds :: TokenParser A.Command
cmds = instr `chainl1` (token (Token ';') >> return A.Sequence) <|> return A.Skip -- $ modified

instr :: TokenParser A.Command -- $ added
instr = alloc <|> cmd

cmd :: TokenParser A.Command
cmd = do
    _ <- token If
    be <- bexpr
    _ <- token Then
    rest <- (do
        c1 <- cmd
        _ <- token Else
        c2 <- cmd
        return [c1, c2]
      ) <|> (do
        c <- cmd
        return [c]
      )
    return $ case rest of
      [c1, c2] -> A.IfThenElse be c1 c2
      [c] -> A.IfThen be c
  <|> do
    _ <- token While
    be <- bexpr
    _ <- token Do
    c <- cmd
    return $ A.While be c
  <|> do
    _ <- token Read
    id_ <- identifier
    return $ A.Read id_
  <|> do
    _ <- token Output
    e <- expr
    return $ A.Output e
  <|> do -- $ added
    _ <- token Return
    e <- expr
    return $ A.Return e
  <|> do
    id_ <- expr
    _ <- token Assign
    e <- expr
    return $ A.Assign id_ e
  <|> do
    _ <- token $ Token '{'
    c <- cmds
    _ <- token $ Token '}'
    return $ A.Environment c -- $ modified
  <|> do -- $ added
    _ <- token Function
    id_ <- decl
    _ <- token $ Token '('
    p <- decls
    _ <- token $ Token ')'
    _ <- token $ Token '{'
    c <- cmds
    _ <- token $ Token '}'
    return $ A.Function id_ p c
  <|> return A.Skip

alloc :: TokenParser A.Command -- $ added
alloc = primitives
  <|> do
    _type <- type_
    _ <- token $ Token '['
    e <- expr
    _ <- token $ Token ']'
    id_ <- identifier
    return $ A.ArrayAlloc _type e id_

decls :: TokenParser A.Command -- $ added
decls = decl `chainl1` (token (Token ';') >> return A.Sequence)

decl :: TokenParser A.Command -- $ added
decl = primitives

params :: TokenParser A.Expression -- $ added
params = error $ "NYI in Functional Parser"

param :: TokenParser A.Expression -- $ added
param = do
    e <- expr
    return $ A.Void

primitives :: TokenParser A.Command -- $ added
primitives = do
    _type <- type_
    id_ <- identifier
    return $ A.Declaration _type id_

expr :: TokenParser A.Expression
expr = term `chainl1` addop

addop :: TokenParser (A.Expression -> A.Expression -> A.Expression)
addop = do { _ <- token $ MathOp Plus ; return $ A.Calculation Plus  }
    <|> do { _ <- token $ MathOp Minus; return $ A.Calculation Minus }

term :: TokenParser A.Expression
term = factor `chainl1` mulop

mulop :: TokenParser (A.Expression -> A.Expression -> A.Expression)
mulop = do { _ <- token $ MathOp Times; return $ A.Calculation Times }
    <|> do { _ <- token $ MathOp DivBy; return $ A.Calculation DivBy }
    <|> do { _ <- token $ MathOp Mod  ; return $ A.Calculation Mod   }

factor :: TokenParser A.Expression
factor = -- $ added
   do -- $ modified
    int <- integer
    return $ A.Integer int
  <|> do -- $ added
    double <- real
    return $ A.Double double
  <|> do
    _ <- token $ MathOp Minus
    e <- factor
    return $ A.Negate e
  <|> do
    _ <- token $ Token '('
    e <- expr
    _ <- token $ Token ')'
    return e

bexpr :: TokenParser A.BoolExpression
bexpr = bterm `chainl1` do { _ <- token $ LogOp Or; return $ A.LogOp Or }

bterm :: TokenParser A.BoolExpression
bterm = bfactor `chainl1` do { _ <- token $ LogOp And; return $ A.LogOp And }

bfactor :: TokenParser A.BoolExpression
bfactor = do
    _ <- token Eof
    return A.Eof
  <|> do
    bool <- boolean
    return $ A.Boolean bool
  <|> do
    _ <- token Not
    be <- bfactor
    return $ A.Not be
  <|> do
    _ <- token $ Token '('
    be <- bexpr
    _ <- token $ Token ')'
    return be
  <|> do
    e1 <- expr
    rel <- relop
    e2 <- expr
    return $ A.Comparison rel e1 e2

-- ** Terminal parsers for terminals with values

token :: Token -> TokenParser Token
token t = do
  tNext <- next
  if removePosition tNext == t then return t else mzero

identifier :: TokenParser String
identifier = do
  t <- next
  case removePosition t of
    Id id -> return id
    _     -> mzero

integer :: TokenParser Int64 -- $ modified
integer = do
  t <- next
  case removePosition t of
    DInt int64 -> return int64
    _             -> mzero

real :: TokenParser Double -- $ added
real = do
  t <- next
  case removePosition t of
    DDouble double -> return double
    _           -> mzero

boolean :: TokenParser Bool
boolean = do
  t <- next
  case removePosition t of
    DBool bool -> return bool
    _            -> mzero

relop :: TokenParser RelOp
relop = do
  t <- next
  case removePosition t of
    RelOp rop -> return rop
    _         -> mzero

type_ :: TokenParser Type -- $ added
type_ = do
  t <- next
  case removePosition t of
    Type _type -> return _type
    _            -> mzero
