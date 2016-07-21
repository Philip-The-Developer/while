{-# LANGUAGE OverloadedStrings #-}
{-|
  Module      : Optimization.Dataflow.GlobalCommonSubexpressions
  Description : Eliminates global common subexpressions.
  Copyright   : 2015, Tay Phuong Ho
  License     : GPL-3
-}
module Optimization.Dataflow.GlobalCommonSubexpressions (
  globalCommonSubexpressions
)
where

import Interface.TAC (
    Command (..), Variable,
    getUseVariables, getDefVariables, renameVariables
  )
import qualified Interface.TAC as TAC

import Prelude (
    Show, Eq,
    FilePath, IO, Int, Maybe (..),
    fst, snd, sum, zip, show, compare, min, max,
    ($), (.), (==), (++), (||), (+),
    String, (&&), not, Ord, zipWith, head, maxBound, (-), Bool(..)
  )
import Data.Functor (
    (<$>)
  )
import Data.Foldable (
    foldl'
  )
import Data.Maybe (
    fromJust
  )
import Data.List (
    filter, nub,
    isInfixOf, last, nub
  )
import Data.List.Split (
    splitOn
  )
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Graph.Inductive (
    Gr, Context, 
    lab, gmap, nmap,
    nodes, edges
  )

import Control.Monad.State (
    State,
    evalState, get, put, return
  )
import qualified Data.String.Utils as String

-- $| This is just a string.
type Expression = String

globalCommonSubexpressions :: Gr ([Command], Set Variable, Set Variable) () -> Gr [Command] ()
globalCommonSubexpressions = nmap removeKillUse . usedExpressions . init3  . postponableExpressions . init2. availableExpressions . init1 . anticipatedExpressions . init0 . nmap calculateKillUse
  where
    calculateKillUse :: ([Command], Set Variable, Set Variable)
                    -> ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression)
    calculateKillUse (cmds, def, use) = (cmds, def, use, exprs, eUsed, eKilled)
      where
        (exprs, eUsed, eKilled) = foldl' foldFunc ([], Set.empty, Set.empty) cmds
        foldFunc (exprs, eUsed, eKilled) cmd = let exprs' = exprs ++ [expr] in if expr == "" then (exprs', eUsed, eKilled) else (exprs', eUsed', eKilled')
          where
            expr = let text = (show cmd)
                       subexpr = last $ splitOn " = " text
                     in if isInfixOf " = " text && (isInfixOf "+" text || isInfixOf "-" text || isInfixOf "*" text || isInfixOf "/" text || isInfixOf "%" text) then subexpr else ""
            eUsed' = (Set.singleton expr) `Set.union` eUsed
            eKilled' = if Set.null $ (Set.fromList $ getUseVariables cmd) `Set.intersection` def then eKilled else (Set.singleton expr) `Set.union` eKilled

    removeKillUse :: ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
                    -> [Command]
    removeKillUse (cmds, _, _, _, _, _, _, _, _, _, _) = cmds

    eAll
      :: Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
            ()
      -> Set Expression
    eAll gr = Set.unions $
              (((\(_,_,_,_,i,_,_,_,_,_,_) -> i) . fromJust . lab gr) <$> nodes gr)
    eAll'
      :: Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression)
            ()
      -> Set Expression
    eAll' gr = Set.unions $
              (((\(_,_,_,_,i,_) -> i) . fromJust . lab gr) <$> nodes gr)

    init0
      :: Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression)
            ()
      -> Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
            ()
    init0 gr = gmap (\(aIn, n, (cmds, def, use, exprs, eUsed, eKilled), aOut) -> let initialization = eAll' gr in (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, initialization, Set.empty, Set.empty, Set.empty, Set.empty), aOut)) gr

    init1, init2, init3
      :: Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
            ()
      -> Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
            ()
    init1 gr = gmap (\(aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, _, _, _, _), aOut) -> let initialization = eAll gr in (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, Set.empty, initialization, Set.empty, Set.empty), aOut)) gr
    init2 gr = gmap (\(aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, _, _, _), aOut) -> let initialization = eAll gr in (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, Set.empty, initialization, Set.empty), aOut)) gr
    init3 gr = gmap (\(aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, postponableIn, _, _), aOut) -> (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, postponableIn, Set.empty, Set.empty), aOut)) gr

    anticipatedExpressions, availableExpressions, postponableExpressions, usedExpressions
      :: Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
            ()
      -> Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
            ()
    anticipatedExpressions gr = dataFlow gr anticipated
    availableExpressions gr  = dataFlow gr available
    postponableExpressions gr = dataFlow gr postponable
    usedExpressions gr  = eliminate (dataFlow gr used)

    anticipated, available, postponable, used, eliminate
      :: Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
            ()
      -> Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
            ()
    anticipated gr = gmap equations gr
      where
        equations :: Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
             -> Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
        equations (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, _, _, e4, e5, e6), aOut) =
          (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn', anticipatedOut', e4, e5, e6), aOut)
          where
            anticipatedIn' = if n == -1 then Set.empty else eUsed `Set.union` (anticipatedOut' `Set.difference` eKilled)
            anticipatedOut' = intersections $
                      (((\(_,_,_,_,_,_,i,_,_,_,_) -> i) . fromJust . lab gr . snd) <$> aOut)
    available gr = gmap equations gr
      where
        equations :: Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
             -> Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
        equations (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, _, _, e5, e6), aOut) =
          (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn', availableOut', e5, e6), aOut)
          where
            availableIn' = intersections $
                      (((\(_,_,_,_,_,_,_,_,i,_,_) -> i) . fromJust . lab gr . fst) <$> aIn' n gr)--Set.singleton $ show $ length aOut
            availableOut' = if n == 0 then Set.empty else (anticipatedIn `Set.union` availableIn') `Set.difference` eKilled
    postponable gr = gmap equations gr
      where
        equations :: Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
             -> Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
        equations (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, _, _, e6), aOut) =
          (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, postponableIn', postponableOut', e6), aOut)
          where
            postponableIn' = intersections $
                      (((\(_,_,_,_,_,_,_,_,_,i,_) -> i) . fromJust . lab gr . fst) <$> aIn' n gr)
            postponableOut' = if n == 0 then Set.empty else (earliest `Set.union` postponableIn') `Set.difference` eUsed
            earliest = anticipatedIn `Set.difference` availableIn
    used gr = gmap equations gr
      where
        equations :: Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
             -> Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
        equations (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, postponableIn, _, _), aOut) =
          (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, postponableIn, usedIn', usedOut'), aOut)
          where
            usedIn' = if n == -1 then Set.empty else (eUsed `Set.union` usedOut') `Set.difference` latest
            usedOut' = Set.unions $
                      (((\(_,_,_,_,_,_,_,_,_,i,_) -> i) . fromJust . lab gr . snd) <$> aOut)
            earliest = anticipatedIn `Set.difference` availableIn
            latest = Set.intersection (earliest `Set.union` postponableIn) $
                      Set.union eUsed $ Set.difference all $
                      intersections $ (((\(_,_,_,_,_,_,anticipatedIn',availableIn',postponableIn',_,_) -> let earliest' = anticipatedIn' `Set.difference` availableIn' in earliest' `Set.union` postponableIn') . fromJust . lab gr . snd) <$> aOut)
            all = eAll gr
    eliminate gr = gmap equations gr
      where
        equations :: Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
             -> Context ([Command], Set Variable, Set Variable
                        , [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression) ()
        equations (aIn, n, (cmds, def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, postponableIn, usedIn, usedOut), aOut) =
          (aIn, n, (cmds', def, use, exprs, eUsed, eKilled, anticipatedIn, availableIn, postponableIn, usedIn, usedOut), aOut)
          where
            cmds' = let (pre, post) = foldl' replace ([], []) $ zipWith (\ cmd expr -> (cmd, expr)) cmds exprs in (nub pre) ++ post
            var expr = expr --let infix_ = if isInfixOf ":double" expr then ":double" else ":int" in (String.replace infix_ "" expr) ++ infix_
            earliest = anticipatedIn `Set.difference` availableIn
            latest = Set.intersection (earliest `Set.union` postponableIn) $
                      Set.union eUsed $ Set.difference all $
                      intersections $ (((\(_,_,_,_,_,_,anticipatedIn',availableIn',postponableIn',_,_) -> let earliest' = anticipatedIn' `Set.difference` availableIn' in earliest' `Set.union` postponableIn') . fromJust . lab gr . snd) <$> aOut)
            all = eAll gr
            replace :: ([Command], [Command]) -> (Command, Expression) -> ([Command], [Command])
            replace (pre, post) (cmd, expr) | Set.member expr $ Set.intersection latest usedOut = (pre ++ [renameVariables cmd (head $ getDefVariables cmd) (var expr)], replace' post (cmd, expr))
            replace (pre, post) (cmd, expr) = (pre, replace' post (cmd, expr))
            replace' :: [Command] -> (Command, Expression) -> [Command]
            replace' post (cmd, expr) | Set.member expr $ Set.intersection eUsed $ Set.union usedOut $ Set.difference all latest = post ++ [TAC.Copy (head $ getDefVariables cmd) (TAC.Variable $ var expr)]
            replace' post (cmd, _) = post ++ [cmd]

    aIn' n gr = filter (\(_,w) -> w == n) (edges gr)

dataFlow
  :: Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
        ()
  -> (Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
         ()
   -> Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
         ())
  -> Gr ([Command], Set Variable, Set Variable, [Expression], Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression, Set Expression)
        ()
dataFlow gr transfer = let next = transfer gr in if gr == next then gr else dataFlow next transfer

intersections :: (Ord a) => [Set a] -> Set a
intersections [] = Set.empty
intersections [a] = a
intersections (a:aa) = foldl' Set.intersection a aa
