{-# LANGUAGE ViewPatterns #-}
{-|
  Module      : ParserGenerator.FileParser
  Description : Reads an
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module ParserGenerator.FileParser (
  parseInput
) where

import Prelude (
    Maybe (..), String, Char,
    lines, takeWhile, dropWhile, not, drop,
    break, fst, words,
    (++), (.), ($), (/=), (==), (||)
  )

import Data.Char (
    isSpace
  )

import Data.List (
    stripPrefix
  )

import Safe (
    headMay
  )

import ParserGenerator.Interface (
    Data (..)
  )

-- | The state of our input parser
data InputState = None | HaskellSection | TokenSection | GrammarSection String

parseInput :: String -> Data
parseInput s = parseInput' (lines s) None (Data "" "" "" [] [] [])


parseInput' :: [String] -> InputState -> Data -> Data

parseInput' [] _ d = d

-- Section changing
parseInput' ("{":s) None d = parseInput' s HaskellSection d
parseInput' ("}":s) HaskellSection d = parseInput' s None d
parseInput' ("%tokens":s) None d = parseInput' s TokenSection d
parseInput' ("%tokens":s) (GrammarSection _) d = parseInput' s TokenSection d
parseInput' ("%grammar":s) None d = parseInput' s (GrammarSection "") d
parseInput' ("%grammar":s) TokenSection d = parseInput' s (GrammarSection "") d

-- None section
parseInput' (('%':'n':'a':'m':'e':' ':rest):s) None d = parseInput' s None d'
  where
    d' = d { functionName = name }
    name = takeWhile (not.isSpace) $ dropWhile isSpace rest

parseInput' ((stripPrefix "%tokentype " -> Just rest):s) None d =
  parseInput' s None d'
  where
    d' = d { tokenType = tt }
    tt = getCode rest

parseInput' (_:s) None d = parseInput' s None d

-- Haskell section
parseInput' (line:s) HaskellSection d = parseInput' s HaskellSection d'
  where
    d' = d { haskellCode = haskellCode d ++ line ++ "\n" }

-- Token section
parseInput' ("":s) TokenSection d = parseInput' s TokenSection d
parseInput' (line:s) TokenSection d = parseInput' s TokenSection d'
  where
    d' = d { tokens = tokens d ++ [(tokenName, tokenCode)]}
    (tokenName, rest) = break isSpace $ dropWhile isSpace line
    tokenCode = getCode rest

-- Grammar section
parseInput' ("":s) is@(GrammarSection _) d = parseInput' s is d

parseInput' (line:s) is@(GrammarSection lhs) d
  | headMay (dropWhile isSpace line) == Just ':'
    || headMay (dropWhile isSpace line) == Just '|'
    = parseInput' s is d'
  where
    rest = dropWhile (\x -> isSpace x || x == ':' || x == '|') line
    (rhs, codePart) = breakCodeAt '{' rest
    d' = d { rules = rules d ++ [(lhs, words rhs, getCode codePart)] }

parseInput' (line:s) (GrammarSection _) d = parseInput' s is' d'
  where
    d' = d { nonTerminals = (lhs', code) : nonTerminals d }
    (lhs', rest) = break isSpace $ dropWhile isSpace line
    code = getCode rest
    is' = GrammarSection lhs'


breakCodeAt :: Char -> String -> (String, String)
breakCodeAt at = getCode' ""
  where
    getCode' :: String -> String -> (String, String)
    -- Premature end of input
    getCode' _ "" = ("", "")

    getCode' "" end@(symb:_)
      | symb == at = ("", end)
    getCode' (t:stack) (h:rest) | t == h = (h:found, end)
      where (found, end) = getCode' stack rest

    getCode' [] (h:rest)
      | h == '"' || h == '\'' = (h:found, end)
      where (found, end) = getCode' [h] rest
    getCode' stack@('}':_) (h:rest)
      | h == '"' || h == '\'' = (h:found, end)
      where (found, end) = getCode' (h:stack) rest

    getCode' [] ('{':rest) = ('{':found, end)
      where (found, end) = getCode' "}" rest
    getCode' stack@('}':_) ('{':rest) = ('{':found, end)
      where (found, end) = getCode' ('}':stack) rest

    getCode' stack (h:rest) = (h:found, end)
      where (found, end) = getCode' stack rest

getCode :: String -> String
getCode = fst . breakCodeAt '}' . drop 1 . dropWhile (/='{')
