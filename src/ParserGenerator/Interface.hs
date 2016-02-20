{-|
    Module      : ParserGenerator.Interface
    Description : A common interface for data shared between multiple modules.
    Copyright   : 2014, Jonas Cleve
    License     : GPL-3
-}
module ParserGenerator.Interface (
  Production, Token, Code, Symbol, Data (..)
) where

import Prelude (
    Show,
    String
  )

type Symbol = String
type Code = String

type Production = (Symbol, [Symbol], Code)
type Token = (Symbol, Code)

data Data = Data
  { haskellCode :: Code
  , functionName :: String
  , tokenType :: Code
  , tokens :: [Token]
  , nonTerminals :: [Token]
  , rules :: [Production]
  } deriving (Show)
