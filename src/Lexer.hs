{-# OPTIONS_HADDOCK ignore-exports #-}
{-|
  Module      : Lexer
  Description : Converts source code given as string to a token stream.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
                2016, Philip Schmiel
  License     : GPL-3
-}
module Lexer (
  Lexer.lex,
  Lexer.lexNamed
) where

import Prelude (
    String, Bool (..),
    break, (==), length, span, read, error, ($), (++), show, (||),
    (&&), (/=), head
  )
import qualified Prelude (
    Double, Char
  )

import Data.Int (
    Int64
  )

import Data.Foldable (
    elem
  )

import Interface.Token (
    PosToken (PosToken),
    Token (..),
    LogOp (..),
    RelOp (..),
    MathOp (..),
    Type (..)
  )
import Interface.Pos (
    SourcePos,
    sourceName, sourceLine, sourceColumn,
    initialPosition, nextLine, nextColumn, incrColumn
  )
import Data.Char (
    isAsciiLower,
    isAsciiUpper,
    isDigit,
    isSpace
  )
import Safe(
    tailSafe
  )

-- * Exported functions

-- | Takes a source code and lazily converts it to a token stream. For example:
--
-- > lex "a := 532" = [Id "a",Assign,Number 532]
lex :: String -> [PosToken]
lex = lexNamed ""

-- | Takes a source code and the name of the code and lazily converts it to a
-- token stream. For example:
--
-- > lexNamed "test.while" "a := 532" = [Id "a",Assign,Number 532]
lexNamed :: String -> String -> [PosToken]
lexNamed name source = process source (initialPosition name)

-- * Helper functions and values

-- | Helper function for 'process'.
process :: String      -- ^ The String
         -> SourcePos   -- ^ Starting Position
         -> [PosToken]   -- ^ Tokens

-- Skip newlines but goto next Line in position counter
process ('\n':source) pos = process source (nextLine pos)

-- Skip whitespaces (all characters evaluated to 'True' by 'Data.Char.isSpace')
process (cur:source) pos
  | isSpace cur = process source (nextColumn pos)

-- Skip single line comments (which start with a #)
process ('#':source) pos = process source'' (nextLine pos)
  where
    -- source' will either be empty or begin with the newline
    (_, source') = break ('\n'==) source
    -- safely (i.e. don't output error on empty list) remove the first element
    -- ('\n') from the list
    source'' = tailSafe source'

-- Assignment: create token "Assign" at current position when matching ":=" and
-- "update" the position for the remaining source incrementing the column by 2
process (':':'=':source) pos =
  PosToken pos Assign : process source (incrColumn pos 2)

-- Relational operators
process ('<':'=':source) pos =
  PosToken pos (RelOp Lte) : process source (incrColumn pos 2)
process ('<':    source) pos =
  PosToken pos (RelOp Lt ) : process source (nextColumn pos)
process ('>':'=':source) pos =
  PosToken pos (RelOp Gte) : process source (incrColumn pos 2)
process ('>':    source) pos =
  PosToken pos (RelOp Gt ) : process source (nextColumn pos)
process ('!':'=':source) pos =
  PosToken pos (RelOp Neq) : process source (incrColumn pos 2)
process ('=':    source) pos =
  PosToken pos (RelOp Eq ) : process source (nextColumn pos)

-- Arithmetic operators
process ('+':source) pos =
  PosToken pos (MathOp Plus ) : process source (nextColumn pos)
process ('-':source) pos =
  PosToken pos (MathOp Minus) : process source (nextColumn pos)
process ('*':source) pos =
  PosToken pos (MathOp Times) : process source (nextColumn pos)
process ('/':source) pos =
  PosToken pos (MathOp DivBy) : process source (nextColumn pos)

-- Identifiers and keywords
process (cur:source) pos
  | isAlpha cur = PosToken pos token : process source' (incrColumn pos l)
    where
      (name, source') = span isAlphaNumeric source
      l = length (cur:name)
      token = case cur:name of
        "true"   -> DBool True
        "false"  -> DBool False
        "not"    -> Not
        "and"    -> LogOp And
        "or"     -> LogOp Or
        "mod"    -> MathOp Mod
        "eof"    -> Eof
        "read"   -> Read
        "output" -> Output
        "return" -> Return        -- $ added
        "if"     -> If
        "then"   -> Then
        "else"   -> Else
        "while"  -> While
        "do"     -> Do
        "int"    -> Type TInt      -- $ added
        "double" -> Type TDouble   -- $ added
        "char"   -> Type TChar
        "function"->Function      -- $ added
        _        -> Id (cur:name)

-- $ Integers and double-precision floating-point numbers
process (cur:source) pos
  | isDigit cur = PosToken pos token : process source' (incrColumn pos l)
    where
      (rest1, s:source1) = span isDigit source
      (rest2, source') = if s == '.' then span isDigit (source1) else ([], s:source1)
      (rest, token) = if s == '.' then (rest1 ++ [s] ++ if rest2 /= [] then rest2 else "0", DDouble (read (cur:rest) :: Prelude.Double))
                      else (rest1, DInt (read (cur:rest) :: Int64))
      l = length (cur:rest)
process (cur:source) pos
  | cur == '.' && isDigit (head source)= PosToken pos token : process source' (incrColumn pos l)
    where
      (rest, source') = span isDigit source
      l = length (cur:rest)
      token = DDouble (read ("0." ++ rest) :: Prelude.Double)

-- Character
process ('\'':c:'\'':source) pos = PosToken pos (DChar (c)):process source (incrColumn pos 3)

-- Single char tokens
process (cur:source) pos
  | cur `elem` tokenCharacters =
    PosToken pos (Token cur) : process source (nextColumn pos)

-- End of source code
process [] _ = []

-- Everything else is a lexical error
process (cur:_) pos = error $ "Lexical error: unexpected '" ++ [cur] ++ "' " ++
  "in file '" ++ sourceName pos ++
  "' on line " ++ show (sourceLine pos) ++
  ", character " ++ show (sourceColumn pos)

{-# ANN tokenCharacters "HLint: ignore Use string literal" #-}
{-# ANN tokenCharacters "HLint: ignore Use String" #-}
-- | List of special characters that should be detected by the lexer
tokenCharacters :: [Prelude.Char]
tokenCharacters = [
    '{', '}',
    '(', ')',
    ';',
    '[', ']' -- $ added
  ]

-- | Returns whether a given character is a character from @[a-zA-Z]@.
isAlpha :: Prelude.Char -> Bool
isAlpha c = isAsciiLower c || isAsciiUpper c

{-# ANN isAlphaNumeric "HLint: ignore Use isAlphaNum" #-}
-- | Returns whether a given character is a character from @[a-zA-Z0-9]@.
isAlphaNumeric :: Prelude.Char -> Bool
isAlphaNumeric c = isAlpha c || isDigit c
