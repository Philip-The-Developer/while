{-|
  Module      : Helper.String
  Description : Helper functions for working with strings.
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Helper.String (
    numberLines, numberLinesAt, replace
) where

import Prelude (
    Eq,
    String, Int, Double,
    replicate, unlines, lines, length, foldr, snd, show, ceiling, logBase,
    fromIntegral,
    (++), (-), ($), (+), (.)
  )
import Data.List (
    intercalate
  )
import Data.List.Split (
    splitOn
  )

numberLinesAt :: Int -> String -> String
numberLinesAt start string = unlines numberedLines
  where
    unnumberedLines :: [String]
    unnumberedLines = lines string

    offset = start - 1

    lastLine :: Int
    lastLine = offset + length unnumberedLines

    numberWidth :: Int
    numberWidth = ceiling $ logBase (10 :: Double) (fromIntegral (lastLine + 1))

    numberedLines :: [String]
    numberedLines = snd $ foldr foldFunc (lastLine, []) unnumberedLines
      where
        foldFunc :: String -> (Int, [String]) -> (Int, [String])
        foldFunc line (lineNo, rest) =
          (lineNo-1, (showNumber lineNo numberWidth ++ ": " ++ line) : rest)

    showNumber :: Int -> Int -> String
    showNumber number width = replicate prefixLength ' ' ++ numberString
      where
        numberString = show number
        prefixLength = width - length numberString


numberLines :: String -> String
numberLines = numberLinesAt 1

replace :: (Eq a) => [a] -> [a] -> [a] -> [a]
replace search replace_ = intercalate replace_ . splitOn search
