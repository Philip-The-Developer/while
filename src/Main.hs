{-# OPTIONS_HADDOCK ignore-exports #-}
{-# LANGUAGE TemplateHaskell #-}
{-|
  Module      : Main
  Description : Compiles a given WHILE program to NASM assembly code.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
  License     : GPL-3
-}
module Main (
  main
) where

import Prelude (
    IO, Maybe (..), Bool (..), FilePath, String, Int,
    putStrLn, show, readFile, unlines, fmap, writeFile, return, foldl, flip, id,
    concat, not, null, unwords,
    ($), (.), (++), (||),
    (>), head, zipWith, unzip, concat
  )
import System.IO (
    hPutStrLn, stderr
  )
import Safe (
    atMay
  )

import Data.List.Split (
    splitOn
  )
import Data.List (
    intercalate
  )
import System.Process (
    createProcess, waitForProcess, proc
  )
import System.Environment (
    getArgs
  )
import System.FilePath (
    dropExtension, addExtension
  )
import System.Directory (
    removeFile
  )

import Data.Maybe (
    fromMaybe, fromJust
  )
import System.Console.GetOpt (
    OptDescr (..), ArgDescr (..), ArgOrder (..),
    getOpt, usageInfo
  )
import Control.Error.Util (
    err
  )
import Control.Monad (
    when
  )
import Data.Functor (
    (<$>)
  )
import Data.FileEmbed (
    embedFile
  )
import Data.ByteString.Char8 (
    unpack
  )

import qualified Lexer as L
import qualified Parser.Functional as FP
import qualified IntermediateCode as IC
import qualified Nasm as N
import qualified Interface.Token as T
import qualified Interface.AST as A
import qualified Optimization.AST as OA
import qualified Optimization.TAC as OT
import qualified Parser.While as W
import qualified Optimization.BasicBlocks as BB
import qualified Optimization.Dataflow.LiveVariables as LV
import qualified GarbageCollection.GarbageCollection as GC

import Helper.String (numberLines, numberLinesAt)
import Helper.List (atLeast)
import Helper.AST (astToPdf, astToDotFile)

data Options = Options
  { optHelp         :: Bool
  , optOutput       :: Maybe FilePath
  , optCleanUp      :: Bool
  , optDebug        :: Bool
  , optGraphs       :: Bool
  , optDotFiles     :: Bool
  , optParser       :: [T.PosToken] -> A.AST
  , optParserName   :: String
  }

defaultOptions :: Options
defaultOptions = Options
  { optHelp         = False
  , optOutput       = Nothing
  , optCleanUp      = True
  , optDebug        = False
  , optGraphs       = False
  , optDotFiles     = False
  , optParser       = W.parse
  , optParserName   = "bottom-up parser"
  }

options :: [OptDescr (Options -> Options)]
options =
  [ Option "h" ["help"        ] (NoArg optionsSetHelp)
      "Show this help and exit"
  , Option "o" ["output"      ] (ReqArg optionsSetOutput "FILE")
      "Output file (default: derived from input file)"
  , Option "i" ["no-cleanup"  ] (NoArg optionsSetCleanUp)
      "Do not clean up intermediate .asm and .o files"
  , Option "d" ["debug"       ] (NoArg optionsSetDebug)
      "Output debug information"
  , Option "g" ["graphs"      ] (NoArg optionsSetGraphs)
      "Output graphs for various compiling phases"
  , Option "f" ["dot-files"   ] (NoArg optionsSetDotFiles)
      "Output graphs as graphviz dot files"
  -- , Option [ ] ["p-parsec"    ] (NoArg optionsSetParsecParser)
  --     "Use the parsec parser"
  , Option "f" ["p-functional"] (NoArg optionsSetFunctionalParser)
      "Use the functional parser"
  -- , Option [ ] ["p-happy"     ] (NoArg optionsSetHappyParser)
  --     "Use the happy parser"
  , Option "b" ["p-bottom-up" ] (NoArg optionsSetBottomUpParser)
      "Use the bottom-up parser (default)"
  ]

optionsSetHelp :: Options -> Options
optionsSetHelp opts = opts { optHelp = True }

optionsSetOutput :: String -> Options -> Options
optionsSetOutput file opts = opts { optOutput = Just file }

optionsSetCleanUp :: Options -> Options
optionsSetCleanUp opts = opts { optCleanUp = False }

optionsSetDebug :: Options -> Options
optionsSetDebug opts = opts { optDebug = True }

optionsSetGraphs :: Options -> Options
optionsSetGraphs opts = opts { optGraphs = True }

optionsSetDotFiles :: Options -> Options
optionsSetDotFiles opts = opts { optDotFiles = True }

-- optionsSetParsecParser :: Options -> Options
-- optionsSetParsecParser opts = opts { optParser = PP.process
--                                    , optParserName = "parsec parser" }

optionsSetFunctionalParser :: Options -> Options
optionsSetFunctionalParser opts = opts { optParser = FP.parse
                                       , optParserName = "functional parser" }

-- optionsSetHappyParser :: Options -> Options
-- optionsSetHappyParser opts = opts { optParser = HP.process . T.removePositions
--                                   , optParserName = "happy parser" }

optionsSetBottomUpParser :: Options -> Options
optionsSetBottomUpParser opts = opts { optParser = W.parse
                                     , optParserName = "bottom-up parser" }

usage :: String
usage = usageInfo "Usage: compiler [OPTION ..] file" options

{-# ANN main "HLint: ignore Use print" #-}
-- | Our main function.
main :: IO ()
main = do
  argv <- getArgs
  let (o, files, errs) = getOpt Permute options argv
  let Options
        { optHelp         = showHelp
        , optOutput       = optOutFile
        , optCleanUp      = cleanUp
        , optDebug        = debugMode
        , optGraphs       = outputGraphs
        , optDotFiles     = outputDotFiles
        , optParser       = parser
        , optParserName   = parserName
        } = foldl (flip id) defaultOptions o
  if showHelp then
    err usage
  else if not $ null errs then
    err (concat errs ++ "\n" ++ usage)
  else if null files || atLeast (2 :: Int) files then
    err ("Error: specify exactly one file to compile\n\n" ++ usage)
  else do
    let inputFile = fromJust $ files `atMay` 0
    let outputFile = fromMaybe (dropExtension inputFile) optOutFile

    sourceCode <- readFile inputFile
    when debugMode $ putStrLn $ "*** source code of '" ++ inputFile ++ "':\n" ++
                              numberLines sourceCode

    let tokenStream = L.lexNamed inputFile sourceCode
    when debugMode $ putStrLn $ "*** token stream:\n" ++
      unwords (show . T.removePosition <$> tokenStream) ++ "\n"

    when debugMode $ putStrLn $ "*** using parser '" ++ parserName ++ "'"

    let ast = parser tokenStream
    when debugMode $ putStrLn $ "*** abstract syntax tree:\n" ++ show ast ++
                                "\n"
    when outputGraphs $ astToPdf ast (addExtension outputFile "ast.pdf")
    when outputDotFiles $ astToDotFile ast (addExtension outputFile "ast.dot")

    let optimizedAST = OA.optimize ast
    when debugMode $ putStrLn $ "*** optimized abstract syntax tree:\n" ++
                                show optimizedAST ++ "\n"
    when outputGraphs $ astToPdf optimizedAST
                          (addExtension outputFile "ast-optimized.pdf")
    when outputDotFiles $ astToDotFile optimizedAST
                          (addExtension outputFile "ast-optimized.dot")

    let (names, intermediateCodes) = unzip $ IC.process optimizedAST -- $ modified
    when debugMode $ putStrLn $ "*** intermediate code:\n" ++
                     numberLines (unlines $ fmap show $ head intermediateCodes) ++ "\n"

    let optimizedIntermediateCodes = fmap OT.optimize intermediateCodes -- $ modified
    when debugMode $ putStrLn $ "*** optimized intermediate code:\n" ++
                     numberLines (unlines $ fmap show $ head optimizedIntermediateCodes)
                     ++ "\n"

    let basicBlockGraphs = fmap BB.tacToGraph optimizedIntermediateCodes -- $ modified
    when outputGraphs $ BB.renderGraph
                        (addExtension outputFile "basic-blocks.pdf")
                        $ head basicBlockGraphs
    when outputDotFiles $ BB.dotGraph
                          (addExtension outputFile "basic-blocks.dot")
                          $ head basicBlockGraphs

    let liveVariablesGraphs = fmap LV.liveVariables basicBlockGraphs -- $ modified
    when outputGraphs $ LV.renderLiveVariablesGraph
                        (addExtension outputFile "live-variables.pdf")
                        $ head liveVariablesGraphs
    when outputDotFiles $ LV.dotLiveVariablesGraph
                          (addExtension outputFile "live-variables.dot")
                          $ head liveVariablesGraphs

    let renamedLVGraphs = fmap LV.renameBlockLocalVariables liveVariablesGraphs -- $ modified
    when outputGraphs $ LV.renderLiveVariablesGraph
                        (addExtension outputFile "live-variables-renamed.pdf")
                        $ head renamedLVGraphs
    when outputDotFiles $ LV.dotLiveVariablesGraph
                          (addExtension outputFile "live-variables-renamed.dot")
                          $ head renamedLVGraphs

    -- let blockDAG = LV.blockDAG liveVariablesGraph

    -- let variablesLiveAtEntry = seq allEmpty $ LV.getVariablesLiveAtEntry liveVariablesGraph
    let variablesLiveAtEntry = LV.getVariablesLiveAtEntry $ head liveVariablesGraphs -- $ modified
    when (not $ null variablesLiveAtEntry) $ hPutStrLn stderr $
      "Warning: The following variables are (possibly) not initialized before "
      ++ "use: " ++ intercalate "," variablesLiveAtEntry

    let liveRanges = fmap LV.variableLiveRanges renamedLVGraphs -- $ modified

    let finishedTACs = fmap (BB.graphToTac . -- $ modified
                                 LV.removeLiveVariableAnnotations) renamedLVGraphs

    let (nasmCodes, frames) = unzip $ zipWith N.process finishedTACs liveRanges   -- $ modified
    when debugMode $ putStrLn $ "*** NASM code:\n" ++ numberLinesAt 140 (head nasmCodes)

    let userDefined_functions = GC.returnSequence names nasmCodes frames -- $ added

    let nasmFile = addExtension outputFile "asm"
    -- template <- readFile "../src/template.asm"
    let template = unpack $ $(embedFile "src/template.asm")
    writeFile nasmFile $ (intercalate ((if (head frames) > 0 then "\nsub rsp, " ++ show (head frames) ++ "\n" else "\n") ++ (head nasmCodes)) $
                                          splitOn ";{-# MAIN CODE #-}" template) ++ (concat userDefined_functions) -- $ modified

    let objectFile = addExtension outputFile "o"
    (_, _, _, pNasm) <- createProcess
                          (proc "nasm" ["-felf64", "-o", objectFile, nasmFile])
    _ <- waitForProcess pNasm

    (_, _, _, pLd) <- createProcess (proc "gcc" ["-o", outputFile, objectFile]) -- $ modified
    _ <- waitForProcess pLd

    when cleanUp $ do
      removeFile nasmFile
      removeFile objectFile

    return ()
