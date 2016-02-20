{-# LANGUAGE MultiWayIf #-}
{-|
  Module      : Nasm.RegisterAllocation
  Description :
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
  License     : GPL-3
-}
module Nasm.RegisterAllocation (
  allocateRegisters
) where

import Prelude (
    Int, Maybe (..),
    compare, snd, fst, head, tail, null, last, init, max,
    ($), (.), (<), (++), (>),
    (&&), (||), not, otherwise 
  )
import Interface.TAC (
    Variable
  )
import Interface.Nasm (
    Register, FRegister, Location (..)
  )
import Data.Functor (
    (<$>)
  )
import Data.Maybe (
    fromJust
  )
import Control.Monad.State (
    State,
    evalState, get, put, return
  )
import Data.Function (
    on
  )
import Data.List (
    sortBy
  )
import qualified Data.Map.Strict as Map
import Data.String.Utils (
    endswith
  )

allocateRegisters :: Map.Map Variable (Int, Int) -> [Register] -> [FRegister] -- $ modified
                  -> (Map.Map Variable Location, Location)
allocateRegisters liveMap registers fregisters = evalState (alloc [] sortedLive)
                                                ( registers
                                                , fregisters
                                                , StackLocation <$> [1..]
                                                , Map.empty
                                                , StackLocation 0
                                                )
  where
    sortedLive = sortBy (compare `on` snd) $ Map.toList liveMap

    alloc :: [(Variable, (Int, Int))] -> [(Variable, (Int, Int))]
          -> State ([Register], [FRegister], [Location], Map.Map Variable Location, Location) -- $ modified
                   (Map.Map Variable Location, Location)
    alloc _ [] = do
      (_, _, _, map, high) <- get -- $ modified
      return (map, high)
    alloc active (new@(var, (start, end)):rest) = do
      active' <- expireOld start active
      (registers, fregisters, stack, map, high) <- get           -- $ modified
      if  | endswith ":double" var && not(null fregisters) -> do -- $ we have fregisters left, so use them
              let f = head fregisters
              put (registers, tail fregisters, stack, Map.insert var (FRegister f) map, high)
              let active'' = sortBy (compare `on` (snd.snd)) $ active' ++ [new]
              alloc active'' rest
          | not(endswith ":double" var) && not(null registers) -> do -- $ we have registers left, so use them
              let r = head registers
              put (tail registers, fregisters, stack, Map.insert var (Register r) map, high)
              let active'' = sortBy (compare `on` (snd.snd)) $ active' ++ [new]
              alloc active'' rest
          | otherwise -> do -- $ there are no more registers left
              let spill = last active'
              if snd (snd spill) > end then do -- give stack location to already
                                               -- assigned variable
                let map' = Map.insert var (fromJust $ Map.lookup (fst spill) map) map
                put ( registers
                    , fregisters -- $ added
                    , tail stack
                    , Map.insert (fst spill) (head stack) map'
                    , max high (head stack)
                    )
                let active'' = sortBy (compare `on` (snd.snd)) $ init active' ++ [new]
                alloc active'' rest
              else do -- Assign stack location to the new live interval
                put ( registers
                    , fregisters -- $ added
                    , tail stack
                    , Map.insert var (head stack) map
                    , max high (head stack)
                    )
                alloc active' rest

    expireOld :: Int -> [(Variable, (Int, Int))]-- $ modified
              -> State ([Register], [FRegister], [Location], Map.Map Variable Location
                       , Location)
                       [(Variable, (Int, Int))]
    expireOld _ [] = return []
    expireOld limit ((var, (_, end)):rest)
      | end < limit = do
        (registers, fregisters, stack, map, high) <- get
        let (registers', fregisters', stack') = case Map.lookup var map of
              Just (Register r) -> (r : registers, fregisters, stack)
              Just (FRegister f) -> (registers, f : fregisters, stack)
              Just s@(StackLocation _) -> (registers, fregisters, s : stack)
              _                 -> (registers, fregisters, stack)
        put (registers', fregisters', stack', map, high)
        expireOld limit rest
    expireOld _ active = return active



