{-# LANGUAGE OverloadedStrings #-}
{-|
  Module      : Helper.AST
  Description : Helper functions for working with AST.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
  License     : GPL-3
-}
module Helper.AST (
  -- * AST functions
  astToDot, astToPdf, astToDotFile
) where

import Interface.AST (
    AST, Command (..), Expression (..), BoolExpression (..),
    showASTPart
  )

import Prelude (
    String, FilePath, IO, Int, show,
    (.), ($), (>>), (+)
  )

import Control.Monad.State (
    State,
    evalState, get, return, modify
  )
import Data.Graph.Inductive (
    Gr, Node,
    empty, insNode, insEdge
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
    Attribute (..), Label (..), Shape (..), Justification (..), Attributes
  )
import Data.Text.Lazy (
    pack
  )

astToDot :: AST -> DotGraph Node
astToDot ast = graphToDot
                  nonClusteredParams{ fmtNode = fn, globalAttributes = ga }
             $ evalState (commandToGraph ast empty) 0
  where
    ga :: [GlobalAttributes]
    ga =
      [ NodeAttrs [ Attr.Shape Attr.Ellipse
                  , Attr.LabelJust Attr.JLeft
                  , Attr.FontName "monospace"
                  ]
      ]
    fn :: (Node, String) -> Attr.Attributes
    fn (_,l) = [(Attr.Label . Attr.StrLabel . pack) l]

    commandToGraph :: Command -> Gr String () -> State Int (Gr String ())
    commandToGraph c_ gr_ = do
      i <- get
      modify (+1)
      commandToGraph' i c_ (insNode (i, showASTPart c_) gr_)
      where
        commandToGraph' :: Int -> Command -> Gr String ()
                        -> State Int (Gr String ())
        commandToGraph' i (Output e) gr = do
          ie <- get
          gr1 <- expressionToGraph e gr
          return $ insEdge (i, ie, ()) gr1
        commandToGraph' i (Return e) gr = do -- $ added
          ie <- get
          gr1 <- expressionToGraph e gr
          return $ insEdge (i, ie, ()) gr1
        commandToGraph' i (Read id_) gr = do
          ii <- get
          gr1 <- expressionToGraph (Void) gr
          return $ insEdge (i, ii, ()) gr1
        commandToGraph' i (Sequence c1 c2) gr = do
          ic1 <- get
          gr1 <- commandToGraph c1 gr
          ic2 <- get
          gr2 <- commandToGraph c2 gr1
          return $ insEdge (i, ic2, ()) $ insEdge (i, ic1, ()) gr2
        commandToGraph' i (IfThen b c) gr = do
          ib <- get
          gr1 <- boolExpressionToGraph b gr
          ic <- get
          gr2 <- commandToGraph c gr1
          return $ insEdge (i, ic, ()) $ insEdge (i, ib, ()) gr2
        commandToGraph' i (IfThenElse b c1 c2) gr = do
          ib <- get
          gr1 <- boolExpressionToGraph b gr
          ic1 <- get
          gr2 <- commandToGraph c1 gr1
          ic2 <- get
          gr3 <- commandToGraph c2 gr2
          return $ insEdge (i, ic2, ()) $ insEdge (i, ic1, ()) $
            insEdge (i, ib, ()) gr3
        commandToGraph' i (While b c) gr = do
          ib <- get
          gr1 <- boolExpressionToGraph b gr
          ic <- get
          gr2 <- commandToGraph c gr1
          return $ insEdge (i, ic, ()) $ insEdge (i, ib, ()) gr2
        commandToGraph' i (Assign id_ e) gr = do
          ii <- get
          gr1 <- expressionToGraph Void gr
          ie <- get
          gr2 <- expressionToGraph e gr1
          return $ insEdge (i, ie, ()) $ insEdge (i, ii, ()) gr2
        commandToGraph' i (Declaration _ id_) gr = do -- $ added
          ii <- get
          gr1 <- expressionToGraph Void gr
          return $ insEdge (i, ii, ()) gr1
        commandToGraph' i (ArrayAlloc _ e id_) gr = do -- $ added
          ie <- get
          gr1 <- expressionToGraph e gr
          ii <- get
          gr2 <- expressionToGraph Void gr1
          return $ insEdge (i, ii, ()) $ insEdge (i, ie, ()) gr2
        commandToGraph' i (Environment c) gr = do -- $ added
          ic <- get
          gr1 <- commandToGraph c gr
          return $ insEdge (i, ic, ()) gr1
        commandToGraph' i (Function t id c2 c3) gr = do -- $ added
          ic1 <- get
          gr1 <- expressionToGraph Void gr
          ic2 <- get
          gr2 <- commandToGraph c2 gr1
          ic3 <- get
          gr3 <- commandToGraph c3 gr2
          return $ insEdge (i, ic3, ()) $ insEdge (i, ic2, ()) $ insEdge (i, ic1, ()) gr3
        commandToGraph' _ _ gr = return gr

    expressionToGraph :: Expression -> Gr String () -> State Int (Gr String ())
    expressionToGraph e_ gr_ = do
      i <- get
      modify (+1)
      expressionToGraph' i e_ (insNode (i, showASTPart e_) gr_)
      where
        expressionToGraph' :: Int -> Expression -> Gr String ()
                           -> State Int (Gr String ())
        expressionToGraph' i (Calculation _ e1 e2) gr = do
          ie1 <- get
          gr1 <- expressionToGraph e1 gr
          ie2 <- get
          gr2 <- expressionToGraph e2 gr1
          return $ insEdge (i, ie2, ()) $ insEdge (i, ie1, ()) gr2
        expressionToGraph' i (Negate e) gr = do
          ie <- get
          gr1 <- expressionToGraph e gr
          return $ insEdge (i, ie, ()) gr1
        expressionToGraph' i (Parameters e1 e2) gr = do -- $ added
          ie1 <- get
          gr1 <- expressionToGraph e1 gr
          ie2 <- get
          gr2 <- expressionToGraph e2 gr1
          return $ insEdge (i, ie2, ()) $ insEdge (i, ie1, ()) gr2
        expressionToGraph' _ _ gr = return gr

    boolExpressionToGraph :: BoolExpression -> Gr String ()
                          -> State Int (Gr String ())
    boolExpressionToGraph b_ gr_ = do
      i <- get
      modify (+1)
      boolExpressionToGraph' i b_ (insNode (i, showASTPart b_) gr_)
      where
        boolExpressionToGraph' :: Int -> BoolExpression -> Gr String ()
                               -> State Int (Gr String ())
        boolExpressionToGraph' i (LogOp _ b1 b2) gr = do
          ib1 <- get
          gr1 <- boolExpressionToGraph b1 gr
          ib2 <- get
          gr2 <- boolExpressionToGraph b2 gr1
          return $ insEdge (i, ib2, ()) $ insEdge (i, ib1, ()) gr2
        boolExpressionToGraph' i (Comparison _ e1 e2) gr = do
          ie1 <- get
          gr1 <- expressionToGraph e1 gr
          ie2 <- get
          gr2 <- expressionToGraph e2 gr1
          return $ insEdge (i, ie2, ()) $ insEdge (i, ie1, ()) gr2
        boolExpressionToGraph' i (Not b) gr = do
          ib <- get
          gr1 <- boolExpressionToGraph b gr
          return $ insEdge (i, ib, ()) gr1
        boolExpressionToGraph' _ _ gr = return gr

astToPdf :: AST -> FilePath -> IO ()
astToPdf ast file = runGraphvizCommand Dot (astToDot ast) Pdf file >> return ()

astToDotFile :: AST -> FilePath -> IO ()
astToDotFile ast file = writeDotFile file (astToDot ast)
