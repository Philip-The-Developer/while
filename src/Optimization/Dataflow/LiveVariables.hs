{-# LANGUAGE OverloadedStrings #-}
{-|
  Module      : Optimization.Dataflow.LiveVariables
  Description : Convert a basic block graph to a graph with live variables
                annotations.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
  License     : GPL-3
-}
module Optimization.Dataflow.LiveVariables (
  liveVariables, renderLiveVariablesGraph, dotLiveVariablesGraph,
  renameBlockLocalVariables, getVariablesLiveAtEntry, variableLiveRanges,
  removeLiveVariableAnnotations
)
where
import Interface.TAC (                
    Command (..), Variable,                
    getUseVariables, getDefVariables, getVariables, renameVariables                
  )

import qualified Interface.TAC as TAC
import Helper.Tuple (
    first, third
  )
import Optimization.Dataflow.GlobalCommonSubexpressions (
    globalCommonSubexpressions
  )

import Prelude (
    Show, Eq,
    FilePath, IO, Int, Maybe (..),
    fst, snd, sum, zip, show, compare, min, max,
    ($), (.), (==), (++), (||), (+),
    String, (&&), not, Ord, zipWith, head, maxBound, (-), dropWhile, (/=), Bool(..)
  )
import Data.Functor (
    (<$>)
  )
import Data.Foldable (
    foldl', foldr
  )
import Data.Function (
    on
  )
import Data.Maybe (
    fromJust
  )
import Data.List (
    intercalate, nub, drop, sortBy, length,
    nub
  )
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Graph.Inductive (
    Gr, Context, Node, LNode,
    lab, gmap, nmap, labNodes
  )

import Data.GraphViz (
    GlobalAttributes (..), DotGraph,
    graphToDot, nonClusteredParams, fmtNode, globalAttributes
  )
import Data.GraphViz.Commands (
    GraphvizCommand (..), GraphvizOutput(..),
    runGraphvizCommand
  )
import Data.GraphViz.Commands.IO (
    writeDotFile
  )
import qualified Data.GraphViz.Attributes.Complete as Attr (
    Attribute (..), Label (..), Shape (..), Justification (..)
  )
import qualified Data.GraphViz.Attributes.HTML as HTML
import qualified Data.GraphViz.Attributes.Colors as Colors
import Data.Text.Lazy (
    pack
  )
import Control.Monad (
    void
  )
import qualified Data.Map.Strict as Map
import Control.Monad.State (
    State,
    evalState, get, put, return
  )

type LiveVariablesGraph = Gr ([Command], Set Variable, Set Variable) ()

getVariablesLiveAtEntry :: LiveVariablesGraph
                        -> [Variable]
getVariablesLiveAtEntry gr = Set.toList $ third $ fromJust $ lab gr 0

removeLiveVariableAnnotations :: LiveVariablesGraph -> Gr [Command] ()
removeLiveVariableAnnotations = nmap first

liveVariables :: Gr [Command] ()
              -> LiveVariablesGraph
liveVariables = nmap removeDefUse . calcLive . nmap calculateDefUse . globalCommonSubexpressions . nmap calculateDefUse
  where
    calculateDefUse :: [Command]
                    -> ([Command], Set Variable, Set Variable)
    calculateDefUse (cmds)= (cmds, def, use)
      where
        (def, use) = foldl' foldFunc (Set.empty, Set.empty) cmds
        foldFunc (defI, useI) cmd = (defO, useO)
          where
            useO = useI `Set.union` (((Set.fromList $ getUseVariables cmd) `Set.difference` defI) `Set.difference` (Set.singleton "%eof%"))
            defO = defI `Set.union` (Set.fromList $ getDefVariables cmd)

    removeDefUse :: ([Command], Set Variable, Set Variable, Set a, Set a)
                 -> ([Command], Set a, Set a)
    removeDefUse (cmds, _, _, s1, s2)= (cmds, s1, s2)

    calcLive
      :: LiveVariablesGraph
      -> Gr ([Command], Set Variable, Set Variable, Set Variable, Set Variable)
            ()
    calcLive g = g''
      where
        g' = nmap (\(c, v1, v2) -> (c, v1, v2, Set.empty, Set.empty)) g
        g'' = fix g'
        fix gr = let next = nextGr gr in if gr == next then gr else fix next

    nextGr
      :: Gr ([Command], Set Variable, Set Variable, Set Variable, Set Variable)
            ()
      -> Gr ([Command], Set Variable, Set Variable, Set Variable, Set Variable)
            ()
    nextGr gr = gmap live gr
      where
        live :: Context ([Command], Set Variable, Set Variable
                        , Set Variable, Set Variable) ()
             -> Context ([Command], Set Variable, Set Variable
                        , Set Variable, Set Variable) ()
        live (aIn, n, (cmds, def, use, _, lOut), aOut) =
          (aIn, n, (cmds, def, use, lIn', lOut'), aOut)
          where
            lIn' = use `Set.union` (lOut `Set.difference` def)
            lOut' = Set.unions $
                      (((\(_,_,_,i,_) -> i) . fromJust . lab gr . snd) <$> aOut)

dotLiveVariablesGraph :: FilePath -> LiveVariablesGraph -> IO ()
dotLiveVariablesGraph file graph = writeDotFile file (dot graph)

renderLiveVariablesGraph :: FilePath
                         -> LiveVariablesGraph
                         -> IO ()
renderLiveVariablesGraph file graph =
  void $ runGraphvizCommand Dot (dot graph) Pdf file

dot :: LiveVariablesGraph -> DotGraph Node
dot graph = graphToDot nonClusteredParams{ fmtNode = fn, globalAttributes = ga }
                       graph
  where
    ga = [ NodeAttrs [ Attr.Shape Attr.BoxShape
                     , Attr.LabelJust Attr.JLeft
                     , Attr.FontName "monospace"
                     ]
         ]
    fn (-1,_) = [(Attr.Label . Attr.StrLabel) "EXIT"]
    fn (0,_) = [(Attr.Label . Attr.StrLabel) "ENTRY"]
    fn (n,(cmds, vIn, vOut)) =
      [ (Attr.Label . Attr.HtmlLabel . HTML.Text) $
        [ HTML.Str . pack $ "B" ++ show n
        , HTML.Newline [HTML.Align HTML.HRight]
        , HTML.Font [HTML.Color $ Colors.RGB 127 127 127]
                    [HTML.Str . pack $ vInStr]
        , HTML.Newline [HTML.Align HTML.HLeft]
        ] ++
        intercalate [HTML.Newline [HTML.Align HTML.HLeft]]
          (((:[]) . HTML.Str . pack . show) <$> cmds)
        ++
        [ HTML.Newline [HTML.Align HTML.HLeft]
        , HTML.Font [HTML.Color $ Colors.RGB 127 127 127]
                    [HTML.Str . pack $ vOutStr]
        , HTML.Newline [HTML.Align HTML.HLeft]
        ]
      ]
      where
        vInStr = "IN={" ++ (if Set.null vIn then ""
                            else intercalate ", " $ Set.toList vIn) ++ "}"
        vOutStr = "OUT={" ++ (if Set.null vOut then ""
                              else intercalate ", " $ Set.toList vOut) ++ "}"

renameBlockLocalVariables :: LiveVariablesGraph -> LiveVariablesGraph
renameBlockLocalVariables = gmap rename
  where
    rename (aI, node, (cmds, in_, out), aO) = (aI, node, (cmds', in_, out), aO)
      where
        cmds' = evalState (rn cmds) (Map.empty, 1)

        rn :: [Command]
           -> State (Map.Map Variable Variable, Int) [Command]
        rn [] = return []
        rn (cmd:rest) = do
          let variables = nub $ getVariables cmd
          cmd' <- rn' cmd variables
          rest' <- rn rest
          return (cmd':rest')

        rn' :: Command -> [Variable]
            -> State (Map.Map Variable Variable, Int) Command
        rn' cmd [] = return cmd
        rn' cmd (v:rest) =
          if Set.member v out || Set.member v in_ || v == "%eof%"
            then rn' cmd rest
          else do
            (map, n) <- get
            case Map.lookup v map of
              Just v' -> rn' (renameVariables cmd v v') rest
              Nothing -> do
                let v' = "t" ++ show n ++ "@" ++ show node ++ dropWhile (/=':') v -- $ modified
                put (Map.insert v v' map, n+1)
                rn' (renameVariables cmd v v') rest

variableLiveRanges :: LiveVariablesGraph
                   -> Map.Map Variable (Int, Int)
variableLiveRanges gr = addToMap 1 Map.empty nodes
  where
    nodes = drop 2 $ sortBy (compare `on` fst) $ labNodes gr

    addToMap :: Int
             -> Map.Map Variable (Int, Int)
             -> [LNode ([Command], Set Variable, Set Variable)]
             -> Map.Map Variable (Int, Int)
    addToMap _ m [] = m
    addToMap gline m ((_, (cmds, in_, out)) : nodes) =
        addToMap (gline + length cmds) m'' nodes
      where
        m' = Set.foldr (Map.adjust (\(s, _) -> (s, gline-1))) m $ Set.difference in_ out
        m'' = snd $ foldl' ff (0, m') cmds

        markLive :: Int -> Variable
             -> Map.Map Variable (Int, Int)
             -> Map.Map Variable (Int, Int)
        markLive _ "%eof%" m = m
        markLive b v m = let b' = if Set.member v out then maxBound else b in
          case Map.lookup v m of
          Just (s, e) -> Map.insert v (min b s, max b' e) m
          Nothing -> Map.insert v (b, b') m

        ff :: (Int, Map.Map Variable (Int, Int))
           -> Command
           -> (Int, Map.Map Variable (Int, Int))
        ff (line, m) cmd =
            (line+1, foldr (markLive (gline + line)) m variables)
          where
            variables = getVariables cmd


