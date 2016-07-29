{-# LANGUAGE OverloadedStrings #-}
{-|
  Module      : Optimization.BasicBlocks
  Description :
  Copyright   : 2014, Jonas Cleve
  License     : GPL-3
-}
module Optimization.BasicBlocks (
  renderGraph, dotGraph, tacToGraph, graphToTac
) where

import Interface.TAC (
    TAC, Command (..), Label,
    isGoto, getLabelFromGoto
  )
import Helper.Tuple (
    third
  )

import Prelude (
    Int, Bool (..), IO, FilePath,
    fst, snd, null, otherwise, last,
    error, show, compare,
    ($), (.), (+), (-), (==), (++)
  )
import Data.Graph.Inductive (
    Gr, Node,
    empty, insNode, insEdge, labNodes
  )
import Data.List (
    intercalate, drop, sortBy, elem
  )
import Data.Foldable (
    foldr, foldl', concatMap
  )
import Data.Functor (
    (<$>)
  )
import Data.Function (
    on
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
import Data.Text.Lazy (
    pack
  )
import Control.Monad (
    void
  )

renderGraph :: FilePath -> Gr [Command] () -> IO ()
renderGraph file graph = void $ runGraphvizCommand Dot (dot graph) Pdf file

dotGraph :: FilePath -> Gr [Command] () -> IO ()
dotGraph file graph = writeDotFile file (dot graph)

dot :: Gr [Command] () -> DotGraph Node
dot graph = graphToDot nonClusteredParams{ fmtNode = fn, globalAttributes = ga }
                       graph
  where
    ga = [ NodeAttrs [ Attr.Shape Attr.BoxShape
                     , Attr.LabelJust Attr.JLeft
                     , Attr.FontName "monospace"
                     ]
         -- , GraphAttrs [Attr.Splines Attr.Ortho]
         ]
    fn (-1,_) = [(Attr.Label . Attr.StrLabel) "EXIT"]
    fn (0,_) = [(Attr.Label . Attr.StrLabel) "ENTRY"]
    fn (n,l) = [(Attr.Label . Attr.StrLabel . pack) $ "B" ++ show n ++ "\\r" ++
                 intercalate "\\l" (show <$> l) ++ "\\l"]

tacToGraph :: TAC -> Gr [Command] ()
tacToGraph tac = graph
  where
    out = if null (fst printing) then snd printing
          else fst printing : snd printing 
    printing = foldr foldfunc start tac
    start = ([], [])

    -- Wraps the list of commands into a list of lists of commands wherein every
    -- sublist is one basic block
    foldfunc c@(Label _) (tl, blocks) = ([c], (tl):blocks)
    foldfunc c@(Goto _) (tl, blocks)
      | null tl   = ([c], blocks)
      | otherwise = ([c], tl:blocks)
    foldfunc c@(GotoCond1 _ _ _) (tl, blocks)
      | null tl   = ([c], blocks)
      | otherwise = ([c], tl:blocks)
    foldfunc c@(GotoCond2 _ _ _ _) (tl, blocks)
      | null tl   = ([c], blocks)
      | otherwise = ([c], tl:blocks)
    foldfunc c (tl, blocks) = (c:tl, blocks)

    blockForLabel :: Label -> Int
    blockForLabel l = blockForLabel' l out 1
      where
        blockForLabel' :: Label -> [[Command]] -> Int -> Int
        blockForLabel' l1 [] _ = error $ "blockForLabel: label " ++ show l1 ++
                                         " not found"
        blockForLabel' l1 (blk : _) n
          | elem (Label l1) blk = n+1
        blockForLabel' l1 (_ : blocks) n = blockForLabel' l1 blocks (n+1)

    graph :: Gr [Command] ()
    graph = third $ foldl' graphCreator (1, True, insNode (0, []) empty)
                                                                     (out++[[]])

    graphCreator :: (Int, Bool, Gr [Command] ()) -> [Command]
                 -> (Int, Bool, Gr [Command] ())
    graphCreator (n, _, gr) [] = (n, False, insEdge (n-1, -1, ()) $
                                                            insNode (-1, []) gr)
    graphCreator (n, edgeToPrev, gr) block = (n+1, edgeToNext, gr''')
      where
        gr' :: Gr [Command] ()
        gr' = insNode (n, block) gr

        gr'' :: Gr [Command] ()
        gr'' = if edgeToPrev then insEdge (n-1, n, ()) gr' else gr'

        gr''' :: Gr [Command] ()
        gr''' = if isGoto (last block) then
            insEdge (n, blockForLabel $ getLabelFromGoto (last block), ()) gr''
          else gr''

        edgeToNext :: Bool
        edgeToNext = case last block of
          Goto _ -> False
          _      -> True

graphToTac :: Gr [Command] () -> TAC
graphToTac gr = concatMap snd $ drop 2 $ sortBy (compare `on` fst) $ labNodes gr
