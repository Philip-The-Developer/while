{-# LANGUAGE OverloadedStrings #-}
{-|
    Module      : ParserGenerator.LRGrammar
    Description : Reads an
    Copyright   : 2014, Jonas Cleve
    License     : GPL-3
-}
module ParserGenerator.LRGrammar
--(
--    createGrammar,
--    i0, closure, goto
--)
where

import Prelude (
    Show, Ord, Eq,
    Int, Maybe (..), String, Bool (..), IO, FilePath,
    filter, drop, fst, elem, fmap, otherwise, error, return, mapM_, mapM, break,
    length, putStrLn, unwords, take, maximum, sum, replicate,
    ($), (.), (==), (&&), (+), (>=), (!!), (-), (||), (>)
  )

import Control.Monad.State (
    State,
    evalState, get, put
  )

import Safe (
    headNote, headMay
  )

import Data.List (
    nub, elemIndex, sort, intercalate, null
  )

import Data.Functor (
    (<$>)
  )

import Data.Foldable (
    any, all, concatMap
  )

import Data.Maybe (
    fromJust
  )

import Helper.Tuple (
    first, second, third
  )

import Helper.List (
    atLeast
  )

import ParserGenerator.Interface (
    Production, Token, Symbol, Code
  )
import qualified ParserGenerator.Interface as I (
    Data (..)
  )

import Data.Set (Set)

import qualified Data.Set as Set

import Data.Graph.Inductive (
    Gr,
    empty, insNode, insEdge
  )
import Data.GraphViz (
    GlobalAttributes (..),
    graphToDot, nonClusteredParams, fmtNode, fmtEdge, globalAttributes
  )
import Data.GraphViz.Commands (
    GraphvizCommand (..), GraphvizOutput(..),
    runGraphvizCommand
  )
import qualified Data.GraphViz.Attributes.Complete as Attr (
    Attribute (..), Label (..), Shape (..), Justification (..), RankType (..)
  )
import Data.Text.Lazy (
    pack
  )
import Control.Monad (
    void
  )

-- import Debug.Trace
import Prelude (show, (++))

type Item = (Production, Int)
type AutomatonItem = (Set Item, [(Symbol, Action)])
type Automaton = (LRGrammar, [AutomatonItem])

data Action
  = Shift Int
  | Goto Int
  | Reduce Int
  | Accept
  | Error
  deriving (Ord, Eq, Show)

data LRGrammar = LR
  { productions :: [Production]
  , tokens :: [Token]
  , startSymbol :: Symbol
  } deriving (Show)

createGrammar :: I.Data -> LRGrammar
createGrammar d = LR { productions = ("%start", [ss], "$1"):prods
                     , tokens = ts
                     , startSymbol = "%start"
                     }
  where
    prods = I.rules d
    ts = I.tokens d
    ss =  (\(x, _, _) -> x) $ headNote "Rules cannot be empty" prods

getProductions :: LRGrammar -> Symbol -> [Production]
getProductions gr symbol = filter ((==symbol) . first) $ productions gr

productionLhs :: Production -> Symbol
productionLhs = first

productionRhs :: Production -> [Symbol]
productionRhs = second

productionCode :: Production -> Code
productionCode = third

endItems :: Set Item -> Set Item
endItems = Set.filter ((==Nothing) . nextSymbol)

nextSymbol :: Item -> Maybe Symbol
nextSymbol ((_, symbols, _), i) = headMay $ drop i symbols

terminals :: LRGrammar -> [Symbol]
terminals gr = nub $ fst <$> tokens gr

isTerminal :: LRGrammar -> Symbol -> Bool
isTerminal gr = (`elem` terminals gr)

nonTerminals :: LRGrammar -> [Symbol]
nonTerminals gr = nub $ first <$> productions gr

isNonTerminal :: LRGrammar -> Symbol -> Bool
isNonTerminal gr = (`elem` nonTerminals gr)

itemizeOne :: Production -> Item
itemizeOne p = (p, 0)

itemize :: [Production] -> Set Item
itemize = Set.fromList . fmap itemizeOne

i0 :: LRGrammar -> Set Item
i0 gr = closure gr $ itemize $ getProductions gr $ startSymbol gr

moveDot :: Item -> Item
moveDot (prod@(_, symbols, _), i)
  | atLeast i symbols = (prod, i+1)
  | otherwise = error "moveDot: cannot move"

-- | Construct the closure of a set of items.
closure :: LRGrammar -> Set Item -> Set Item
-- Add all items themselves to the set (1. argument) and also have the algorithm
-- check all of them for possible nonkernel items (3. argument)
closure gr i = closure' i Set.empty i
  where
    -- the items already constructed
    -- -> the nonterminals already added for nonkernel items (those with
    --        the dot at the beginning)
    -- -> the items to look at
    -- -> the result
    closure' :: Set Item -> Set String -> Set Item -> Set Item
    -- We have no more items to look at => we're done
    closure' items _ lookItems
      | Set.null lookItems = items
    -- We need to have a look at one of items in lookItems
    closure' items nts lookItems = closure' items' nts' lookItems''
      where
        -- Take first element we have to look at …
        item = Set.elemAt 0 lookItems
        -- … and remove it
        lookItems' = Set.deleteAt 0 lookItems
        -- Get next symbol to be recognized
        nextMay = nextSymbol item
        -- If there is a symbol which is 1. a nonterminal and 2. not yet
        -- seen → add all nonkernel items of this symbol to our set
        (items', nts', lookItems'') = case nextMay of
          Just next ->
            if isNonTerminal gr next && Set.notMember next nts then
              -- construct the nonkernel items
              let newItems = itemize $
                    filter ((==next).first) $ productions gr
              in ( Set.union items newItems
                 , Set.insert next nts
                 , Set.union lookItems' newItems
                 )
            else
              (items, nts, lookItems')
          _ -> (items, nts, lookItems')

-- | For the grammar definition @gr@ calculate GOTO(@items@, @symbol@) in 3
--   simple steps:
--   1. Filter out all items that don't have @symbol@ as next grammar symbol
--   2. For all remaining items move the dot one symbol to right
--   3. Calculate the closure
goto :: LRGrammar -> Symbol -> Set Item -> Set Item
goto gr symbol items = closure gr $ Set.map moveDot $
                                Set.filter ((== Just symbol) . nextSymbol) items

firstSet :: LRGrammar -> [Symbol] -> Set Symbol
firstSet _ [] = Set.singleton ""
firstSet gr (symbol:symbols) = Set.union symbolSetWithoutEpsilon symbolsSet
  where
    symbolSet = firstSetOfOne gr symbol
    symbolSetWithoutEpsilon = Set.delete "" symbolSet
    symbolsSet = if Set.member "" symbolSet then
        firstSet gr symbols
      else
        Set.empty

firstSetOfOne :: LRGrammar -> Symbol -> Set Symbol
firstSetOfOne gr symb = evalState (go symb) Set.empty
  where
    go :: Symbol -> State (Set Symbol) (Set Symbol)
    go symbol
      | isTerminal gr symbol = return $ Set.singleton symbol
      | isNonTerminal gr symbol = do
        lookSymbols <- get
        if Set.member symbol lookSymbols then
            return Set.empty
          else do
            put $ Set.insert symbol lookSymbols
            let rhss = productionRhs <$> getProductions gr symbol
            firstSubSets <- mapM goRhs rhss
            return $ Set.unions firstSubSets

    goRhs :: [Symbol] -> State (Set Symbol) (Set Symbol)
    goRhs [] = return $ Set.singleton ""
    goRhs s = goRule s

    goRule :: [Symbol] -> State (Set Symbol) (Set Symbol)
    goRule [] = return Set.empty
    goRule (symbol:symbols) = do
      subFirstSet <- go symbol
      let subFirstSetWithoutEpsilon = Set.delete "" subFirstSet
      if nullable gr symbol then do
        nextFirstSet <- goRule symbols
        let nextFirstSetWithoutEpsilon = Set.delete "" nextFirstSet
        return $ Set.union subFirstSetWithoutEpsilon nextFirstSetWithoutEpsilon
      else
        return subFirstSetWithoutEpsilon

followSet :: LRGrammar -> Symbol -> Set Symbol
followSet gr symb = evalState (go symb) Set.empty
  where
    go :: Symbol -> State (Set Symbol) (Set Symbol)
    go symbol
      | isNonTerminal gr symbol = do
        lookSymbols <- get
        if Set.member symbol lookSymbols then
            return Set.empty
          else do
            put $ Set.insert symbol lookSymbols
            let initialSet = if symbol == startSymbol gr then
                  Set.singleton "$"
                else
                  Set.empty
            let prods = filter ((symbol `elem`) . second) $ productions gr
            sets <- prodFollow prods
            return $ Set.unions (initialSet:sets)
      where
          prodFollow :: [Production] -> State (Set Symbol) [Set Symbol]
          prodFollow [] = return [Set.empty]
          prodFollow (prod:prods) = do
            let (_, _:rest) = break (==symbol) $ second prod
            let prods' = if symbol `elem` rest then
                  (first prod, rest, third prod):prods else prods
            let firstSetRest = firstSet gr rest
            if Set.member "" firstSetRest then do
                followParent <- go $ first prod
                follows <- prodFollow prods'
                return $ Set.delete "" firstSetRest : followParent : follows
              else do
                follows <- prodFollow prods'
                return $ firstSetRest : follows

nullable :: LRGrammar -> Symbol -> Bool
nullable gr = nullable' Set.empty
  where
    nullable' :: Set Symbol -> Symbol -> Bool
    nullable' symbols symbol
      -- Terminals never derive epsilon
      | isTerminal gr symbol = False
      -- A loop won't do either
      | Set.member symbol symbols = False
      -- There is one chance though
      | otherwise = any (all (nullable' newSymbols)) prods
      where
        newSymbols = Set.insert symbol symbols
        -- Get all productions belonging to the symbol
        prods = productionRhs <$> getProductions gr symbol

lr0Items :: LRGrammar -> [Set Item]
lr0Items gr = items [i0 gr] 0 (terminals gr ++ nonTerminals gr)
  where
    items :: [Set Item] -> Int -> [Symbol] -> [Set Item]
    items itemSets i []
      | i+1 >= length itemSets = itemSets
      | otherwise = items itemSets (i+1) (terminals gr ++ nonTerminals gr)
    items itemSets i (symb:symbs) = items itemSets' i symbs
      where
        set = itemSets !! i
        gotoSet = goto gr symb set
        itemSets' = if gotoSet `elem` itemSets || Set.null gotoSet then itemSets
          else itemSets ++ [gotoSet]

printItemSets :: [Set Item] -> IO ()
printItemSets = printItemSets' 0
  where
    printItemSets' :: Int -> [Set Item] -> IO ()
    printItemSets' _ [] = return ()
    printItemSets' i (set:rest) = do
      putStrLn "========================================"
      putStrLn $ "  State " ++ show i
      let list = Set.toList set
      mapM_ printItem list
      printItemSets' (i+1) rest
      where
        printItem :: Item -> IO ()
        printItem ((lhs, rhs, _), j) =
          putStrLn $ lhs ++ " → " ++ unwords (take j rhs ++ ["•"] ++ drop j rhs)

lr0Automaton :: LRGrammar -> Automaton
lr0Automaton gr = (gr, automaton 0)
  where
      items = lr0Items gr

      automaton :: Int -> [AutomatonItem]
      automaton i
        | i >= length items = []
        | otherwise = (itemSet, gotos ++ reduces) : automaton (i+1)
        where
          itemSet = items !! i
          gotos = concatMap go (terminals gr ++ nonTerminals gr)
          reduces = concatMap re $ Set.toList $ endItems itemSet

          go :: Symbol -> [(Symbol, Action)]
          go s = if Set.null set then [] else [(s, action)]
            where
              set = goto gr s itemSet
              action
                | isTerminal gr s    = Shift $ fromJust $ elemIndex set items
                | isNonTerminal gr s = Goto $ fromJust $ elemIndex set items
                | otherwise          = Error

          re :: Item -> [(Symbol, Action)]
          re (prod@(lhs, _, _), _) = fmap
            (\s -> ( s
                   , if s == "$" && lhs == startSymbol gr then Accept
                     else Reduce $ fromJust $ elemIndex prod (productions gr)
                   )
            ) $ Set.toList $ followSet gr lhs

showAutomaton :: Automaton -> String
showAutomaton (lr, items) = showRules 0 (productions lr) ++
                            showAutomaton' 0 items
  where
    showRules :: Int -> [Production] -> String
    showRules i ps = showRules' i ps
      where
        maxLen :: Int
        maxLen = 12 + maximum (
            (\(x, y, _) -> length x + sum (length <$> y) + length y) <$> ps
          )

        combine :: String -> String -> String
        combine x y = x ++ replicate (maxLen - length x) ' ' ++ "{" ++ y ++ "}"

        showRules' :: Int -> [Production] -> String
        showRules' _ [] = ""
        showRules' j ((lhs, rhs, code):prods) = combine
          ("RULE " ++ show j ++ ": " ++ lhs ++ " → " ++ unwords rhs) code
          ++ "\n" ++ showRules' (j+1) prods

    showAutomaton' :: Int -> [AutomatonItem] -> String
    showAutomaton' _ [] = ""
    showAutomaton' i ((set, gotos):rest) = "============================" ++
                                           "============\n  State " ++
                                           show i ++ "\n\n" ++
                                           concatMap showItem (sort list)
                                           ++ "\n" ++
                                           concatMap showGoto (sort gotos)
                                           ++ "\n" ++
                                           showAutomaton' (i+1) rest
      where
        list = Set.toList set

        showItem :: Item -> String
        showItem ((lhs, rhs, _), j) =
          lhs ++ " → " ++ unwords (take j rhs ++ ["•"] ++ drop j rhs) ++ "\n"

        showGoto :: (Symbol, Action) -> String
        showGoto (s, Goto j) = "    " ++ s ++ " GOTO " ++ show j ++ "\n"
        showGoto (s, Shift j) = "    " ++ s ++ " SHIFT " ++ show j ++ "\n"
        showGoto (s, Reduce j) = "    " ++ s ++ " REDUCE " ++ show j ++ "\n"
        showGoto (s, Accept) = "    " ++ s ++ " ACCEPT\n"

automatonGraph :: Automaton -> Gr (Set Item) (Symbol)
automatonGraph (_, items_) = insert 0 items_ $ insNode (-1, Set.empty) empty
  where
    insert :: Int -> [AutomatonItem] -> Gr (Set Item) (Symbol)
           -> Gr (Set Item) (Symbol)
    insert _ [] gr = gr
    insert n ((itemSet, actions):items) gr = insert (n+1) items gr2
      where
        gr1 = if Set.null itemSet then gr else insNode (n, itemSet) gr
        gr2 = insertNodes actions gr1

        insertNodes :: [(Symbol, Action)] -> Gr (Set Item) (Symbol)
                    -> Gr (Set Item) (Symbol)
        insertNodes [] gr_ = gr_
        insertNodes ((symbol, action):actions_) gr_ = insertNodes actions_ $
          case action of
            Shift m -> insEdge (n, m, symbol) gr_
            Goto m  -> insEdge (n, m, symbol) gr_
            Accept -> insEdge (n, -1, "$") gr_
            _ -> gr_

renderGraph :: FilePath -> Gr (Set Item) (Symbol) -> IO ()
renderGraph file graph = void $ runGraphvizCommand Dot dot Pdf file
  where
    dot = graphToDot nonClusteredParams{ fmtNode = fn
                                       , fmtEdge = fe
                                       , globalAttributes = ga
                                       }
                     graph
    ga = [ NodeAttrs [ Attr.Shape Attr.BoxShape
                     , Attr.LabelJust Attr.JLeft
                     , Attr.FontName "Gentium"
                     ]
         , GraphAttrs [ Attr.Rank Attr.SameRank
                      , Attr.NodeSep 0.3
                      ]
         , EdgeAttrs [ Attr.FontName "Gentium"
                     , Attr.LabelDistance 1.0
                     ]
         ]

    fn (-1,_) = [ Attr.Label $ Attr.StrLabel "accept"
                ]

    fn (n,l) = [(Attr.Label . Attr.StrLabel . pack) $ "I_" ++ show n ++ "\\r" ++
                 intercalate "\\l" (showItem <$> (Set.toList (kernelItems l)))
                 ++ "\\l" ++ compactKIs
               ]
      where
        nonKernelItems = Set.toList $ packNonkernel l
        compactKIs = if null nonKernelItems then ""
                     else (intercalate ", " nonKernelItems ++ "\\l")

    fe (_, _, l) = [ (Attr.HeadLabel . Attr.StrLabel . pack) l
                   , (Attr.TailLabel . Attr.StrLabel . pack) l
                   ]

    kernelItems :: Set Item -> Set Item
    kernelItems = Set.filter (\((lhs, _, _), n) -> lhs == "%start" || n > 0)

    packNonkernel :: Set Item -> Set Symbol
    packNonkernel set = Set.map (\((lhs, _, _), _) -> lhs) $
      Set.difference set (kernelItems set)

showItem :: Item -> String
showItem ((lhs, rhs, _), j) =
  lhs ++ " → " ++ unwords (take j rhs ++ ["•"] ++ drop j rhs)
