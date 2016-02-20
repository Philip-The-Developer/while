{-# LANGUAGE TemplateHaskell #-}
{-|
  Module      : Main
  Description : A program which (given a grammar definition file) creates a
                bottom-up parser.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Main (
  main
) where

import Prelude (
    IO, Int,
    putStrLn, readFile, writeFile, show, head,
    (++), ($), (||), (!!), (==), (&&)
  )

import Control.Monad (
    when
  )

import System.Environment (
    getArgs
  )

import System.FilePath (
    replaceExtension
  )

import ParserGenerator.FileParser (
    parseInput
  )

import ParserGenerator.Generator (
    generateCode
  )

import ParserGenerator.LRGrammar (
    createGrammar, lr0Automaton, showAutomaton, automatonGraph, renderGraph
  )
import Helper.List (
    exactly
  )
import Data.FileEmbed (
    embedFile
  )
import Data.ByteString.Char8 (
    unpack
  )

import Language.Haskell.Exts

-- | The main function.
main :: IO ()
main = do
  args <- getArgs
  if exactly (1 :: Int) args ||
     exactly (2 :: Int) args && head args == "-d" then do
    let grammarFile = args !! (if exactly (1 :: Int) args then 0 else 1)
    let debug = exactly (2 :: Int) args
    let haskellFile = replaceExtension grammarFile "hs"
    let outputFile = replaceExtension grammarFile "txt"
    content <- readFile grammarFile
    let data_ = parseInput content
    let grammar = createGrammar data_
    -- template <- readFile "src/ParserGenerator/Template.hs"
    let template = unpack $ $(embedFile "src/ParserGenerator/Template.hs")
    let code = generateCode template data_ (lr0Automaton grammar)
    writeFile haskellFile code
    when debug $ writeFile outputFile (showAutomaton (lr0Automaton grammar))
    when debug $ renderGraph (replaceExtension grammarFile "pdf") $
                                          automatonGraph $ lr0Automaton grammar
    when debug $ putStrLn $ prettyPrint $ fromParseResult $ parseFileContents $
      "x=" ++ show data_
    when debug $ putStrLn $ prettyPrint $ fromParseResult $ parseFileContents $
      "x=" ++ show (lr0Automaton grammar)
  else
    putStrLn "Error: specify one command line parameter"


