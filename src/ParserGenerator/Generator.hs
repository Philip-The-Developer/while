{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-|
    Module      : ParserGenerator.Generator
    Description : Generates the haskell code for a parser from an LR automaton.
    Copyright   : 2014, Jonas Cleve
    License     : GPL-3
-}
module ParserGenerator.Generator (
  generateCode
) where

import ParserGenerator.LRGrammar (
    Automaton, LRGrammar (..), AutomatonItem, Action (..),
    productionLhs, productionRhs, productionCode, isTerminal
  )
import ParserGenerator.Interface (
    Production, Data (nonTerminals, tokenType, haskellCode, functionName)
  )
import Helper.Tuple (
    first, second
  )
import Helper.String (
    replace
  )
import Helper.List (
    atMost
  )

import Prelude (
    String, Maybe (..), Int, Bool (..),
    fst, show, snd, filter, length, otherwise, head, not,
    (++), ($), (.), (+), (-), (==), (||)
  )
import Data.Foldable (
    concatMap, foldr, concat
  )
import Data.Functor (
    (<$>)
  )
import Data.List.Split (
    splitOn
  )
import Data.List (
    stripPrefix, elemIndex, nub, lookup, intercalate, isInfixOf, reverse
  )
import Data.Maybe (
    fromJust, isJust
  )
import Text.Printf (
    printf
  )

generateCode :: String -> Data -> Automaton -> String
generateCode template data_ automaton = haskellCode data_ ++ filledTemplate
  where
    filledTemplate :: String
    filledTemplate = concatMap fill $ splitOn "-- TEMPLATE:" template

    fill :: String -> String
    fill (stripPrefix "INPUT_TYPE\n" -> Just rest) =
      tokenType data_ ++ rest
    fill (stripPrefix "RESULT_TYPE\n" -> Just rest) =
      head (productionRhs (head (productions (fst automaton)))) ++ rest
    fill (stripPrefix "FUNCTION_NAME\n" -> Just rest) =
      functionName data_ ++ rest
    fill (stripPrefix "OUTPUT_TYPE\n" -> Just rest) =
      fromJust (
        lookup
          (head (productionRhs (head (productions (fst automaton)))))
          (nonTerminals data_)
      ) ++ rest
    fill (stripPrefix "STACK_ELEMENTS\n" -> Just rest) =
      "= StackTerminal " ++ tokenType data_ ++ "\n" ++ stackElements ++ rest
    fill (stripPrefix "LHS_LIST\n" -> Just rest) = show lhsList ++ "\n" ++ rest
    fill (stripPrefix "REDUCE_LIST\n" -> Just rest) = show reduceList ++ "\n" ++
                                                      rest
    fill (stripPrefix "GOTO\n" -> Just rest) = gotos ++ "\n" ++ rest
    fill (stripPrefix "STATE\n" -> Just rest) = states ++ "\n" ++ rest
    fill (stripPrefix "REDUCE\n" -> Just rest) = reduces ++ "\n" ++ rest
    fill x = x

    lhsList :: [Int]
    lhsList = (fromJust . (`elemIndex` lhss) . first) <$>
                                                    productions (fst automaton)

    lhss :: [String]
    lhss = nub $ first <$> productions (fst automaton)

    reduceList :: [Int]
    reduceList = (length . second) <$> productions (fst automaton)

    stackElements :: String
    stackElements = concatMap
      (\(lhs, code) -> "  | StackElement_" ++ lhs ++ " " ++ code ++ "\n")
      (nonTerminals data_)

    gotos :: String
    gotos = gotos' 0 (snd automaton)
      where
        gotos' :: Int -> [AutomatonItem] -> String
        gotos' _ [] = ""
        gotos' n (ai:ais) = concatMap gen gotoActions ++ gotos' (n+1) ais
          where
            gen (nt, Goto s) = printf "goto %d %d = %d\n"
                                            n (fromJust (nt `elemIndex` lhss)) s
            gotoActions =
              filter (\(_, act) -> case act of { Goto _ -> True; _ -> False })
                (snd ai)

    states :: String
    states = states' 0 (snd automaton)
      where
        states' :: Int -> [AutomatonItem] -> String
        states' _ [] = ""
        states' n (ai:ais)
          | atMost (0 :: Int) (snd ai) = states' (n+1) ais
          | otherwise =
              printf "state states@(%d:_) stack input = case headMay input of\n"
                n ++
               concatMap gen actions ++
               printf ("  _ -> error $ \"unexpected \" ++\n               " ++
                "if null input then \"end of file\" else show (head input)\n" ++
                "               ++ \"\\nexpecting %s\"\n") expected ++
               states' (n+1) ais
          where
            gen (nt, Shift s) =
              printf "  %s -> shift %d states stack input\n" (formatNt nt) s
            gen (nt, Reduce r) =
              printf "  %s -> reduce %d states stack input\n" (formatNt nt) r
            gen (nt, Accept) =
              printf "  %s -> accept states stack input\n" (formatNt nt)
            actions =
              filter (\(_, act) -> case act of { Goto _ -> False; _ -> True })
                (snd ai)

            formatNt "$" = "Nothing"
            formatNt nt =
              "Just (" ++
              replace "$$" "_" (fromJust (lookup nt (tokens (fst automaton))))
              ++ ")"

            expected :: String
            expected = intercalate ", " $
              filter (\x -> (||) (x == "'eof'") $ isJust $
                                              lookup x (tokens (fst automaton)))
              (((\x -> if x == "$" then "'eof'" else x) . fst) <$> snd ai)

    reduces :: String
    reduces = reduces' 0 $ productions $ fst automaton
      where
        reduces' :: Int -> [Production] -> String
        reduces' _ [] = ""
        reduces' n (prod:prods) =
          printf ("reduce %d states (%sstack) input =\n  (reduceAndGoto %d " ++
                  "states, StackElement_%s (%s) : stack, input)\n")
                  n stack n stackType newStack ++ reduces' (n+1) prods
          where
            stackType :: String
            stackType = if prodLhs == "%start" then head (productionRhs prod)
                                               else prodLhs
              where
                prodLhs = productionLhs prod

            stack :: String
            stack = concat $ reverse $ stackElems 1 $ productionRhs prod

            stackElems :: Int -> [String] -> [String]
            stackElems _ [] = []
            stackElems m (symb:symbs)
              | not (isInfixOf ("$" ++ show m) (productionCode prod)) =
                  "_ : " : stackElems (m+1) symbs
              | isTerminal (fst automaton) symb =
                ((
                  if | isInfixOf "$$" tokenCode ->
                        "StackTerminal (" ++
                        replace "$$" ("v" ++ show m) tokenCode ++ ")"
                     | otherwise ->
                        "StackTerminal v" ++ show m
                ) ++ " : ") : stackElems (m+1) symbs
              | otherwise = ("StackElement_" ++ symb ++ " v" ++ show m ++ " : ")
                              : stackElems (m+1) symbs
              where
                tokenCode :: String
                tokenCode = fromJust $ lookup symb (tokens $ fst automaton)

            newStack :: String
            newStack = snd $ foldr placeholderReplace
                              (length $ productionRhs prod, productionCode prod)
                              (productionRhs prod)

            placeholderReplace :: String -> (Int, String) -> (Int, String)
            placeholderReplace _ (m, code) =
              (m-1, replace ("$" ++ show m) ("v" ++ show m) code)
