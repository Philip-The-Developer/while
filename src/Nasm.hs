{-# OPTIONS_HADDOCK ignore-exports #-}
{-# LANGUAGE MultiWayIf #-}
{-|
  Module      : Nasm
  Description : Creates nasm assembly output from intermediate code
                representation.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
  License     : GPL-3
-}
module Nasm (
  Nasm.process
) where

import Interface.Nasm (
    NasmCode,
    Register (..), FRegister (..), Location (..), Operand (..), Immediate (..),
    Instruction (..),
    toCode, operandIsImmediate, operandIsImmediateDouble, operandIsLocation, operandIsRegister, operandIsFRegister,
    operandIsStackLocation,
    mov, add, sub, imul, imul', idiv, cmp, neg, push, pop, shl, sar, instr,
    mov', fmov, fadd, fsub, fmul, fdiv, fcmp, fneg
  )

import Control.Monad.State (
    State,
    evalState, get, return, put
  )
-- import Data.Map.Map.Lazy (
--     Map.Map,
--     empty, lookup, insert
--   )
import Prelude (
    Monad,
    String, Maybe (..), Int, Bool (..),
    unlines, show, not, otherwise, round, logBase, fromIntegral, abs, flip, fst,
    ($), (++), (==), (/=), (-), (>), (||), (&&), (*), (.), (<), (>=), (<=), (+), snd, filter
  )
import Data.Functor (
    fmap,
    (<$>)
  )
import Data.Maybe (
    fromJust
  )
import Data.Bits (
    popCount
  )
import Data.Int (
    Int64
  )
import Data.List (
    filter, head, dropWhile, elem
  )
import Control.Monad (
    when
  )
import Data.String.Utils (
    endswith, replace
  )

import qualified Data.Map.Strict as Map
import qualified Interface.TAC as TAC

import Nasm.RegisterAllocation (
    allocateRegisters
  )

type StateContent = ( Map.Map TAC.Variable Location   -- The mapping var -> loc
                    , Location                        -- The highest loc used
                    , Map.Map TAC.Variable (Int, Int) -- Live range data
                    , Int                             -- Current line number
                    )

availableRegisters :: [Register]
availableRegisters = [RBX, RCX, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15]

-- $ added
availableFRegisters :: [FRegister]
availableFRegisters = [XMM1, XMM2, XMM3, XMM4, XMM5, XMM6, XMM7, XMM8, XMM9, XMM10, XMM11, XMM12, XMM13, XMM14, XMM15]

allLocations :: [Location]
allLocations = (Register <$> availableRegisters) ++ (StackLocation <$> [1..])

-- $ added
allFLocations :: [Location]
allFLocations = (FRegister <$> availableFRegisters) ++ (StackLocation <$> [1..])

-- $| Takes three address code, converts it into NASM source code and determines the size of the stack frame.
process :: TAC.TAC -> Map.Map TAC.Variable (Int, Int) -> (String, Int) -- $ modified
process tac liveData = (\(a,b) -> (unlines a,b)) $
  evalState (generate tac) (locMap, high, liveData, 1)
  where
    (locMap, high) = allocateRegisters liveData availableRegisters availableFRegisters

-- | Tries to look up the given variable in the internal hash map; adds it to
-- map if it cannot be found.
getLocation :: TAC.Variable -> State StateContent Location
getLocation v = do
  (m, _, _, _) <- get
  let loc = Map.lookup v m
  case loc of
    Just l -> return l

-- | Returns a free register which is only to be used for one generated
-- IC instruction and therefore not removed from the list.
getTemporary :: State StateContent Location
getTemporary = do
  (m, high, liveData, line) <- get
  let blocked = (flip Map.lookup m . fst) <$>
         (filter (\(_, (x, y)) -> x <= line && y >= line) $ Map.assocs liveData)
  let temp = head $ dropWhile (flip elem blocked . Just) allLocations
  when (temp > high) $ put (m, temp, liveData, line)
  return temp

-- $| Returns a free floating point register which is only to be used for one generated
-- IC instruction and therefore not removed from the list.
getFTemporary :: State StateContent Location
getFTemporary = do
  (m, high, liveData, line) <- get
  let blocked = (flip Map.lookup m . fst) <$>
         (filter (\(_, (x, y)) -> x <= line && y >= line) $ Map.assocs liveData)
  let temp = head $ dropWhile (flip elem blocked . Just) allFLocations
  when (temp > high) $ put (m, temp, liveData, line)
  return temp

-- -- | Returns the memory location or the direct representation of the given
-- -- datum.
-- getValue :: TAC.Data -> State StateContent String
-- getValue (TAC.Variable "%eof%") = return "%eof%"
-- getValue (TAC.Variable v) = do
--   loc <- getLocation v
--   return $ toCode loc
-- getValue (TAC.Immediate i) = return $ show i

-- | Converts a IC datum to an assembly operand.
dataToOperand :: TAC.Data -> State StateContent Operand
dataToOperand (TAC.Variable v) = variableToOperand v
dataToOperand (TAC.ImmediateInteger i) = return $ Immediate $ ImmediateInt i   -- $ modified
dataToOperand (TAC.ImmediateDouble i) = return $ Immediate $ ImmediateDouble i -- $ added

-- | Converts a IC variable to an assembly operand.
variableToOperand :: TAC.Variable -> State StateContent Operand
variableToOperand v = do
  loc <- getLocation v
  return $ Location loc

-- $| Generates the assembly code from an AST using the helper function
-- `generate'`, puts entry & exit code around and determines the size of the stack frame.
generate :: TAC.TAC -> State StateContent ([String], Int) -- $ modified
generate tac = do
  code <- generate' tac
  (_, high, _, _) <- get
  return $ case high of
    StackLocation int | int > 0 -> (code, (8*(int-1)))
    _ ->  (code, 0)

-- | Generates the assembly code from an AST.
generate' :: TAC.TAC -> State StateContent [String]
generate' [] = return []
generate' (hd:rst) = do
  code <- case hd of
    TAC.Read v -> do
      o <- variableToOperand v
      return $ (Call "input_number") : case o of
        Location (Register RAX) -> []
        _ -> force [mov o rax]

    TAC.Output d -> do
      o <- dataToOperand d
      let preCode = case o of
            Location (Register RAX) -> []
            _ -> force [mov rax o]
      return $ preCode ++ [(Call "output_number")]

    TAC.Pop v -> do -- $ added
      o <- variableToOperand v
      case o of
        Location (FRegister _) -> returnCode [pop rax
                                             , mov o rax]
        _ -> returnCode [pop o]

    TAC.Push d -> do -- $ added
      o <- dataToOperand d
      case o of
        Location (FRegister _) -> returnCode [mov rax o
                                             , push rax]
        (Immediate (ImmediateDouble _)) -> returnCode [mov' o
                                                      , push rax]
        _ -> returnCode [push o]

    TAC.FRead v -> do -- $ added
      o <- variableToOperand v
      returnCode $ [push $ Immediate $ ImmediateInt 0
                   , instr "call input_float"
                   , if o == Location (FRegister XMM0) then Nothing else fmov o xmm0
                   , pop rax]

    TAC.FOutput d -> do -- $ added
      o <- dataToOperand d
      let preCode = case o of
            Location (FRegister XMM0) -> []
            (Immediate (ImmediateDouble _)) -> force [ mov' o
                                                     , mov xmm0 rax ]
            _ -> force [fmov xmm0 o]
      return $ preCode ++ force [push $ Immediate $ ImmediateInt 0, instr "call output_float", pop rax]

    TAC.Return d -> do -- $ added
      o <- dataToOperand d
      returnCode [mov (Location (Register RBX)) o
                 , instr $ "jmp .return_sequence"]

    TAC.FReturn d -> do -- $ added
      o <- dataToOperand d
      returnCode [fmov xmm0 o
                 , instr $ "jmp .return_sequence"]

    TAC.Copy v d -> do -- modified
      o1 <- variableToOperand v
      o2 <- dataToOperand d
      return $
        if | o1 == o2 -> []
           | operandIsImmediateDouble o2 -> force [ mov' o2, mov o1 rax ] -- $ added
           | operandIsFRegister o1 || operandIsFRegister o2 -> force [ fmov o1 o2 ] -- $ added
           | otherwise -> case mov o1 o2 of
              Just code -> [code]
              Nothing -> force [ mov rax o2 -- $ fixed
                               , mov o1 rax
                               ]

    TAC.Convert v d -> do -- $ added
      o1 <- variableToOperand v
      o2 <- dataToOperand d
      returnCode [instr $ "cvtsi2sd " ++ toCode o1 ++ ", " ++ toCode o2]

    TAC.ArrayAlloc v (TAC.ImmediateInteger 0) -> do -- $ added
      o1 <- variableToOperand v
      returnCode [mov o1 (Immediate $ ImmediateInt 0)]

    TAC.ArrayAlloc v d -> do -- $ added
      o1 <- variableToOperand v
      o2 <- dataToOperand d
      let (pre, o2') = if operandIsImmediate o2 then ([mov rdx o2], rdx) else ([], o2)
      returnCode $ pre ++ 
                 [instr "multipush rcx, rsi, rdi, r8, r9, r10, r11"
                 , push o2'
                 , imul' rdi o2' (Immediate $ ImmediateInt 8)
                 , add rdi (Immediate $ ImmediateInt 8)
                 , instr "call malloc"
                 , instr "test rax, rax"
                 , instr "jz alloc_error"
                 , instr "pop QWORD [rax]"
                 , instr "multipop rcx, rsi, rdi, r8, r9, r10, r11"
                 , mov o1 rax]

    TAC.ArrayDealloc v -> do -- $ added
      o <- variableToOperand v
      returnCode [instr "multipush rcx, rsi, rdi, r8, r9, r10, r11"
                 , mov rdi o
                 , instr "call free"
                 , instr "multipop rcx, rsi, rdi, r8, r9, r10, r11"]

    TAC.ArrayCopy v d@(TAC.Variable v2) -> do -- $ added
      o1 <- variableToOperand v
      o2 <- dataToOperand d
      pre <- cond2Code (TAC.Variable v) d
      let label = "." ++ (replace ":" "?" $ replace "]" "" $ replace "[" "" v) ++ "~" ++ (replace ":" "?" $ replace "]" "" $ replace "[" "" v2)
      return $
        if | o1 == o2 -> []
           | otherwise -> pre ++ force [instr $ "je " ++ label
                                       , instr "multipush rcx, rsi, rdi, r8, r9, r10, r11"
                                       , mov rdi o1
                                       , instr "call free"
                                       , instr "multipop rcx, rsi, rdi, r8, r9, r10, r11"
                                       , instr $ label ++ ":"]

    TAC.FromArray v1 v2 d -> do -- $ added
      o1 <- variableToOperand v1
      o2 <- variableToOperand v2
      o3 <- dataToOperand d
      l <- getTemporary
      let (pre1, o1') = if not $ operandIsRegister o1 then ([mov (Location l) o1], (Location l)) else ([], o1)
      let (pre2, o2') = if not $ operandIsRegister o2 then ([mov rax o2], rax) else ([], o2)
      let (pre3, o3') = if not $ operandIsRegister o3 then ([mov rdx o3], rdx) else ([], o3)
      returnCode $ pre1 ++ pre2 ++ pre3 ++
                 [instr $ "cmp " ++ toCode o3' ++ ", [" ++ toCode o2' ++ "]"
                 , instr "jge index_error"
                 , instr $ "cmp " ++ toCode o3' ++ ", 0"
                 , instr "jl index_error"
                 , instr $ (if operandIsFRegister o1' then "movq " else "mov ") ++ toCode o1' ++ ", [" ++ toCode o2' ++ "+" ++ toCode o3' ++ "*8+8]"]
                 ++ if o1' /= o1 then [mov o1 o1'] else []

    TAC.ToArray v d1 d2 -> do -- $ added
      (o1, o2, o3) <- getOperands v d1 d2
      l <- getTemporary
      let (pre1, o1') = if not $ operandIsRegister o1 then ([mov rax o1], rax) else ([], o1)
      let (pre2, o2') = if not $ operandIsRegister o2 then ([mov rdx o2], rdx) else ([], o2)
      let (pre3, o3') = if operandIsImmediateDouble o3 then ([mov' o3], rax) else if not $ operandIsRegister o3 then ([mov (Location l) o3], (Location l)) else ([], o3)
      returnCode $ pre1 ++ pre2 ++ pre3 ++
                 [instr $ "cmp " ++ toCode o2' ++ ", [" ++ toCode o1' ++ "]"
                 , instr "jge index_error"
                 , instr $ "cmp " ++ toCode o2' ++ ", 0"
                 , instr "jl index_error"
                 , instr $ (if operandIsFRegister o3' then "movq " else "mov ") ++ "[" ++ toCode o1' ++ "+" ++ toCode o2' ++ "*8+8], " ++ toCode o3']

    TAC.Add v d1 d2 -> do
      (o1, o2, o3) <- getOperands v d1 d2
      if o1 == o2 || o1 == o3 then do
        -- One of the source operands is the same as the destination operand
        let o2' = if o1 == o2 then o3 else o2
        return $ case add o1 o2' of
          Just code -> [code]
          -- If both operands are memory locations we have to copy around a bit
          Nothing -> force [ mov rax o2'
                           , add o1 rax
                           ]

      -- None of the source operands is the same as the destination operand
      else if operandIsRegister o1 then do
        let (o2', o3') = if operandIsStackLocation o2 then (o2, o3)
                                                      else (o3, o2)
        returnCode [ mov o1 o2'
                   , add o1 o3'
                   ]
      else if not (operandIsStackLocation o2) &&
              not (operandIsStackLocation o3) then
        -- Destination operand is a memory location but none of the source
        -- operands is
        returnCode [ mov o1 o2
                   , add o1 o3
                   ]
      else
        -- Just use RAX as intermediate register
        returnCode [ mov rax o2
                   , add rax o3
                   , mov o1 rax
                   ]

    TAC.Sub v d1 d2 -> do
      (o1, o2, o3) <- getOperands v d1 d2
      if o1 == o2 && (operandIsRegister o1 || not (operandIsLocation o3)) then
        returnCode [sub o1 o3]
      else if o1 /= o3 && operandIsRegister o1 then
        returnCode [ mov o1 o2
                   , sub o1 o3
                   ]
      else
        returnCode [ mov rax o2
                   , sub rax o3
                   , mov o1 rax
                   ]

    TAC.Mul v d1 d2 -> do
      (o1, o2, o3) <- getOperands v d1 d2

      -- Determine whether to work with the three operand or two operand version
      -- of IMUL
      if operandIsImmediate o2 || operandIsImmediate o3 then do
        -- Work with three operand version
        let (o2', o3') = if operandIsImmediate o3 then (o2, o3) else (o3, o2)

        -- Test whether the immediate operand is a power of two
        if isPowerOf2 o3' then do
          -- Shift instead of multiplication
          let (o1', pre, post) = if operandIsRegister o1 ||
                                    operandIsRegister o2' then (o1, [], [])
                                 else (rax, [mov rax o1], [mov o1 rax])
          let o3v = getValue o3'
          let (negS, _) = (o3v < 0, round $ logBase 2 (fromIntegral o3v))
          returnCode $ pre ++ (if o2' == o1' then [] else [mov o1' o2']) ++
                       [shl o1' o3'] ++ (if negS then [neg o1'] else []) ++ post

        else if operandIsImmediate o2' then do
          -- This should never be reached (optimized away earlier)
          returnCode [mov o1 (Immediate $ ImmediateInt $
                                                  getValue o2' * getValue o3')]

        else do
          -- o3' is Immediate but not 2^i, o2' is not immediate
          case imul' o1 o2' o3' of
            Just code -> return [code]
            -- The only case why it does not work is that o1 is no register
            Nothing -> returnCode [ imul' rax o2' o3'
                                  , mov o1 rax
                                  ]

      else do
        -- Work with two operand version

        -- If destination is not a register make it one
        let (o1', pre, post) = if operandIsRegister o1 then (o1, [], [])
                               else (rax, [mov rax o1], [mov o1 rax])

        let (pre2, o2') = if o1' == o2 then ([], o3)
                          else if o1' == o3 then ([], o2)
                          else ([mov o1' o2], o3)

        returnCode $ pre ++ pre2 ++ [imul o1' o2'] ++ post

    TAC.Div v d1 d2 -> do
      (o1, o2, o3) <- getOperands v d1 d2

      -- Determine whether we can shift instead of dividing
      if operandIsImmediate o2 && isPowerOf2 o2 ||
         operandIsImmediate o3 && isPowerOf2 o3 then do
        -- Shift
        let (o2', o3') = if operandIsImmediate o3 then (o2, o3) else (o3, o2)
        let (o1', pre, post) = if operandIsRegister o1 then (o1, [], [])
                               else (rax, [mov rax o1], [mov o1 rax])
        let o3v = getValue o3'
        let (negS, bits) = (o3v < 0, round $ logBase 2 (fromIntegral $ abs o3v))
        returnCode $ pre ++ (if o2' == o1' then [] else [mov o1' o2']) ++
                     [ instr $ "lea rdx, [" ++ toCode o1' ++ "+" ++
                         show ((abs o3v) - 1) ++ "]"
                     , add o1 (Immediate (ImmediateInt 0))
                     , instr $ "cmovs " ++ toCode o1 ++ ", rdx"
                     , sar o1' (Immediate (ImmediateInt bits))
                     ] ++
                     (if negS then [neg o1'] else []) ++ post

      else do
        -- Use normal division
        (pre, o3') <- if operandIsImmediate o3 then do
            l <- getTemporary
            return ([mov (Location l) o3], Location l)
          else return ([], o3)
        returnCode $ pre ++ [mov rax o2, instr "cqo", idiv o3', mov o1 rax]

    TAC.Mod v d1 d2 -> do
      (o1, o2, o3) <- getOperands v d1 d2
      (pre, o3') <- if operandIsImmediate o3 then do
          l <- getTemporary
          return ([mov (Location l) o3], Location l)
        else return ([], o3)
      returnCode $ pre ++ [mov rax o2, instr "cqo", idiv o3', mov o1 rdx]

    TAC.Neg v d -> do
      o1 <- variableToOperand v
      o2 <- dataToOperand d
      let pre = if | o1 == o2 -> []
                   | otherwise -> case mov o1 o2 of
                      Just code -> [code]
                      Nothing -> force [ mov rax o1
                                       , mov o2 rax
                                       ]
      return $ pre ++ force [neg o1]

    TAC.FAdd v d1 d2 -> do -- $ added
      (o1, o2, o3) <- getOperands v d1 d2
      (pre, o2', o3') <- immediate2FLocation o2 o3
      if  | o1 == o2' || o1 == o3' -> do
            let o2'' = if o1 == o2' then o3' else o2' in
                if  | operandIsRegister o1 -> 
                              if  | operandIsRegister o2'' -> 
                                        returnCode $ pre ++ [ fadd o1 o2'' ]
                                          | otherwise ->
                                            returnCode $ pre ++ [ fmov xmm0 o2''
                                                  , fadd o1 xmm0 ]
                                | operandIsRegister o2'' ->
                                  returnCode $ pre ++ [ fmov xmm0 o1
                                    , fadd xmm0 o2''
                                    , fmov o1 xmm0 ]
                                | otherwise ->
                                  returnCode $ pre ++ [ fmov xmm0 o1
                                    , fadd xmm0 o2''
                                    , fmov o1 xmm0 ]
                  | operandIsRegister o1 ->
                    if  | operandIsRegister o3' ->
                                  returnCode $ pre ++ [ fmov o1 o2'
                                    , fadd o1 o3' ]
                            | otherwise ->
                                  returnCode $ pre ++ [ fmov o1 o2'
                                    , fmov xmm0 o3'
                                    , fadd o1 xmm0 ]
                  | otherwise ->
                if  | operandIsRegister o2' -> 
                                  returnCode $ pre ++ [ fmov xmm0 o3'
                                    , fadd xmm0 o2'
                                    , fmov o1 xmm0 ]
                                | operandIsRegister o3' ->
                                  returnCode $ pre ++ [ fmov xmm0 o2'
                                    , fadd xmm0 o3'
                                    , fmov o1 xmm0 ]
                                | otherwise ->
                                  returnCode $ pre ++ [ fmov xmm0 o2'
                                    , fadd xmm0 o3'
                                    , fmov o1 xmm0 ]

    TAC.FSub v d1 d2 -> do -- $ added
      (o1, o2, o3) <- getOperands v d1 d2
      (pre, o2', o3') <- immediate2FLocation o2 o3
      if  | o1 == o2' || o1 == o3' -> do
            let o2'' = if o1 == o2' then o3' else o2' in
                if  | operandIsRegister o1 -> 
                              if  | operandIsRegister o2'' -> 
                                        returnCode $ pre ++ [ fsub o1 o2'' ]
                                          | otherwise ->
                                            returnCode $ pre ++ [ fmov xmm0 o2''
                                                  , fsub o1 xmm0 ]
                                | operandIsRegister o2'' ->
                                  returnCode $ pre ++ [ fmov xmm0 o1
                                    , fsub xmm0 o2''
                                    , fmov o1 xmm0 ]
                                | otherwise ->
                                  returnCode $ pre ++ [ fmov xmm0 o1
                                    , fsub xmm0 o2''
                                    , fmov o1 xmm0 ]
                  | operandIsRegister o1 ->
                    if  | operandIsRegister o3' ->
                                  returnCode $ pre ++ [ fmov o1 o2'
                                    , fsub o1 o3' ]
                            | otherwise ->
                                  returnCode $ pre ++ [ fmov o1 o2'
                                    , fmov xmm0 o3'
                                    , fsub o1 xmm0 ]
                  | otherwise ->
                if  | operandIsRegister o2' -> 
                                  returnCode $ pre ++ [ fmov xmm0 o3'
                                    , fsub xmm0 o2'
                                    , fmov o1 xmm0 ]
                                | operandIsRegister o3' ->
                                  returnCode $ pre ++ [ fmov xmm0 o2'
                                    , fsub xmm0 o3'
                                    , fmov o1 xmm0 ]
                                | otherwise ->
                                  returnCode $ pre ++ [ fmov xmm0 o2'
                                    , fsub xmm0 o3'
                                    , fmov o1 xmm0 ]

    TAC.FMul v d1 d2 -> do -- $ added
      (o1, o2, o3) <- getOperands v d1 d2
      (pre, o2', o3') <- immediate2FLocation o2 o3
      if  | o1 == o2' || o1 == o3' -> do
            let o2'' = if o1 == o2' then o3' else o2' in
                if  | operandIsRegister o1 -> 
                              if  | operandIsRegister o2'' -> 
                                        returnCode $ pre ++ [ fmul o1 o2'' ]
                                          | otherwise ->
                                            returnCode $ pre ++ [ fmov xmm0 o2''
                                                  , fmul o1 xmm0 ]
                                | operandIsRegister o2'' ->
                                  returnCode $ pre ++ [ fmov xmm0 o1
                                    , fmul xmm0 o2''
                                    , fmov o1 xmm0 ]
                                | otherwise ->
                                  returnCode $ pre ++ [ fmov xmm0 o1
                                    , fmul xmm0 o2''
                                    , fmov o1 xmm0 ]
                  | operandIsRegister o1 ->
                    if  | operandIsRegister o3' ->
                                  returnCode $ pre ++ [ fmov o1 o2'
                                    , fmul o1 o3' ]
                            | otherwise ->
                                  returnCode $ pre ++ [ fmov o1 o2'
                                    , fmov xmm0 o3'
                                    , fmul o1 xmm0 ]
                  | otherwise ->
                if  | operandIsRegister o2' -> 
                                  returnCode $ pre ++ [ fmov xmm0 o3'
                                    , fmul xmm0 o2'
                                    , fmov o1 xmm0 ]
                                | operandIsRegister o3' ->
                                  returnCode $ pre ++ [ fmov xmm0 o2'
                                    , fmul xmm0 o3'
                                    , fmov o1 xmm0 ]
                                | otherwise ->
                                  returnCode $ pre ++ [ fmov xmm0 o2'
                                    , fmul xmm0 o3'
                                    , fmov o1 xmm0 ]

    TAC.FDiv v d1 d2 -> do -- $ added
      (o1, o2, o3) <- getOperands v d1 d2
      (pre, o2', o3') <- immediate2FLocation o2 o3
      if  | o1 == o2' || o1 == o3' -> do
            let o2'' = if o1 == o2' then o3' else o2' in
                if  | operandIsRegister o1 -> 
                              if  | operandIsRegister o2'' -> 
                                        returnCode $ pre ++ [ fdiv o1 o2'' ]
                                          | otherwise ->
                                            returnCode $ pre ++ [ fmov xmm0 o2''
                                                  , fdiv o1 xmm0 ]
                                | operandIsRegister o2'' ->
                                  returnCode $ pre ++ [ fmov xmm0 o1
                                    , fdiv xmm0 o2''
                                    , fmov o1 xmm0 ]
                                | otherwise ->
                                  returnCode $ pre ++ [ fmov xmm0 o1
                                    , fdiv xmm0 o2''
                                    , fmov o1 xmm0 ]
                  | operandIsRegister o1 ->
                    if  | operandIsRegister o3' ->
                                  returnCode $ pre ++ [ fmov o1 o2'
                                    , fdiv o1 o3' ]
                            | otherwise ->
                                  returnCode $ pre ++ [ fmov o1 o2'
                                    , fmov xmm0 o3'
                                    , fdiv o1 xmm0 ]
                  | otherwise ->
                if  | operandIsRegister o2' -> 
                                  returnCode $ pre ++ [ fmov xmm0 o3'
                                    , fdiv xmm0 o2'
                                    , fmov o1 xmm0 ]
                                | operandIsRegister o3' ->
                                  returnCode $ pre ++ [ fmov xmm0 o2'
                                    , fdiv xmm0 o3'
                                    , fmov o1 xmm0 ]
                                | otherwise ->
                                  returnCode $ pre ++ [ fmov xmm0 o2'
                                    , fdiv xmm0 o3'
                                    , fmov o1 xmm0 ]

    TAC.FNeg v d -> do -- $ added
      o1 <- variableToOperand v
      o2 <- dataToOperand d
      if | o1 == o2 ->
               if  | operandIsRegister o1 -> 
                         returnCode [ fneg o1 ]
               | otherwise ->
                                 returnCode [ mov rax o1
                                   , instr "xor rax, [sign_mask]"
                                   , mov o1 rax ]
         | otherwise ->
               if  | operandIsRegister o1 ->
                                 returnCode [ fmov o1 o2
                                   , fneg o1 ]
               | otherwise ->
                                 returnCode [ mov rax o2
                                   , instr "xor rax, [sign_mask]"
                                   , mov o1 rax ]

    TAC.Goto l -> returnCode [instr $ "jmp ." ++ l]

    TAC.GotoCond1 l TAC.IsTrue d -> do
      pre <- cond1Code d
      return $ pre ++ force [instr $ "jne ." ++ l]

    TAC.GotoCond1 l TAC.IsFalse d -> do
      pre <- cond1Code d
      return $ pre ++ force [instr $ "je ." ++ l]

    TAC.GotoCond2 l TAC.Equal d1 d2 -> do
      pre <- cond2Code d1 d2
      return $ pre ++ force [instr $ "je ." ++ l]

    TAC.GotoCond2 l TAC.NotEqual d1 d2 -> do
      pre <- cond2Code d1 d2
      return $ pre ++ force [instr $ "jne ." ++ l]

    TAC.GotoCond2 l TAC.Greater d1 d2 -> do
      pre <- cond2Code d1 d2
      return $ pre ++ force [instr $ "jg ." ++ l]

    TAC.GotoCond2 l TAC.GreaterEqual d1 d2 -> do
      pre <- cond2Code d1 d2
      return $ pre ++ force [instr $ "jge ." ++ l]

    TAC.GotoCond2 l TAC.Less d1 d2 -> do
      pre <- cond2Code d1 d2
      return $ pre ++ force [instr $ "jl ." ++ l]

    TAC.GotoCond2 l TAC.LessEqual d1 d2 -> do
      pre <- cond2Code d1 d2
      return $ pre ++ force [instr $ "jle ." ++ l]

    TAC.GotoCond2 l TAC.FEqual d1 d2 -> do         -- $ added
      pre <- fcond2Code d1 d2
      return $ pre ++ force [instr $ "je ." ++ l]

    TAC.GotoCond2 l TAC.FNotEqual d1 d2 -> do      -- $ added
      pre <- fcond2Code d1 d2
      return $ pre ++ force [instr $ "jne ." ++ l]

    TAC.GotoCond2 l TAC.FGreater d1 d2 -> do       -- $ added
      pre <- fcond2Code d1 d2
      return $ pre ++ force [instr $ "ja ." ++ l]

    TAC.GotoCond2 l TAC.FGreaterEqual d1 d2 -> do  -- $ added
      pre <- fcond2Code d1 d2
      return $ pre ++ force [instr $ "jae ." ++ l]

    TAC.GotoCond2 l TAC.FLess d1 d2 -> do          -- $ added
      pre <- fcond2Code d1 d2
      return $ pre ++ force [instr $ "jb ." ++ l]

    TAC.GotoCond2 l TAC.FLessEqual d1 d2 -> do     -- $ added
      pre <- fcond2Code d1 d2
      return $ pre ++ force [instr $ "jbe ." ++ l]

    TAC.Label l -> returnCode [instr $ "." ++ l ++ ":"]

    TAC.Call v l -> do                             -- $ added
      o1 <- variableToOperand v
      returnCode $ if l == "length_" then
          [pop rax
          , instr $ "mov rax, [rax]"
          , mov o1 rax]
        else
          [instr $ "call " ++ l
          , if endswith ":double" v then mov o1 xmm0 else mov o1 rax]

  (m, high, liveData, line) <- get
  put (m, high, liveData, line+1)
  rest <- generate' rst
  return $ ("; " ++ show hd):(fmap toCode code ++ rest)
  where
    rax, rdx, rdi, xmm0 :: Operand
    rax = (Location (Register RAX))
    rdx = (Location (Register RDX))
    rdi = (Location (Register RDI))
    xmm0 = (Location (FRegister XMM0)) -- $ added

    returnCode :: (Monad m, NasmCode c) => [Maybe c] -> m [c]
    returnCode = return . force

    force :: [Maybe c] -> [c]
    force = fmap fromJust

    getValue :: Operand -> Int64
    getValue (Immediate (ImmediateInt x)) = x

    isPowerOf2 :: Operand -> Bool
    isPowerOf2 (Immediate (ImmediateInt x)) =
      popCount   x  == 1 && x > 0 ||
      popCount (-x) == 1 && x < 0
    isPowerOf2 _ = False

    getOperands :: TAC.Variable -> TAC.Data -> TAC.Data
                -> State StateContent (Operand, Operand, Operand)
    getOperands v d1 d2 = do
      o1 <- variableToOperand v
      o2 <- dataToOperand d1
      o3 <- dataToOperand d2
      return (o1, o2, o3)

    cond1Code :: TAC.Data -> State StateContent [Instruction]
    cond1Code d = do
      code <- case d of
        TAC.Variable "%eof%" -> return "%eof%"
        _ -> do
          o <- dataToOperand d
          return $ toCode o
      let (preCode, loc) = if code == "%eof%" then ([instr "call eof"], "rax")
                                              else ([], code)
      returnCode $ preCode ++ [instr $ "cmp QWORD " ++ loc ++ ", 0"]

    cond2Code :: TAC.Data -> TAC.Data -> State StateContent [Instruction]
    cond2Code d1 d2 = do
      o1 <- dataToOperand d1
      o2 <- dataToOperand d2
      if operandIsRegister o1 ||
         operandIsStackLocation o1 && not (operandIsStackLocation o2) then
        returnCode [cmp o1 o2]
      else do
        temp <- getTemporary
        returnCode [mov (Location temp) o1, cmp o1 o2]

    fcond2Code :: TAC.Data -> TAC.Data -> State StateContent [Instruction] -- $ added
    fcond2Code d1 d2 = do
      o1 <- dataToOperand d1
      o2 <- dataToOperand d2
      (pre, o1', o2') <- immediate2FLocation o1 o2
      if operandIsRegister o1' then
            returnCode $ pre ++ [fcmp o1' o2']
      else
        returnCode $ pre ++ [fmov xmm0 o1', fcmp xmm0 o2']

    immediate2FLocation :: Operand -> Operand -> State StateContent ([Maybe Instruction], Operand, Operand) -- $ added
    immediate2FLocation o2 o3 = do
      temp <- getFTemporary
      (pre, o2') <-
                if | operandIsImmediate o2 -> return ([ mov' o2, mov (Location temp) rax ], (Location temp))
                   | otherwise -> return ([], o2)
      (pre', o3') <-
            if | operandIsImmediate o3 -> return ([ mov' o3, mov (Location temp) rax ], (Location temp))
               | otherwise -> return ([], o3)
      return (pre ++ pre', o2', o3')
