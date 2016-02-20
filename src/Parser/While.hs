{-|
  Module      : Parser.While
  Description : A generated bottom-up LR parser for the WHILE language.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
                2016, Philip Schmiel
  License     : GPL-3
-}
module Parser.While (parse) where

import Interface.Token
import qualified Interface.AST as AST


import Safe (
    headMay
  )

import Prelude (
    Show,
    Int, Maybe (Just, Nothing),
    drop, head, tail, error, show, null,
    (!!), ($), (++)
  )

{-# ANN module "HLint: ignore" #-}

-- | The value stack consists of various stack elements.
type Stack = [StackElement]
-- | States are just integers.
type State = Int
-- | The state stack consists of various states.
type StateStack = [State]
-- | Rules are just numbers.
type RuleNumber = Int
-- | Non-terminals are just numbers.
type NonTerminal = Int
-- | The user-defined input type.
type Input = [ PosToken ]
-- | The user-defined output type (the type of the first rule).
type Output =  AST.AST 
-- | The first constructor is for all tokens and the following constructors are
--   for the respective non-terminal symbols.
data StackElement
  = StackTerminal  PosToken 
  | StackElement_Param  AST.Expression 
  | StackElement_Params  AST.Expression 
  | StackElement_Decls  AST.Command 
  | StackElement_Decl  AST.Command 
  | StackElement_Alloc  AST.Command 
  | StackElement_Primitives  AST.Command 
  | StackElement_Bfactor  AST.BoolExpression 
  | StackElement_Bterm  AST.BoolExpression 
  | StackElement_Bexpr  AST.BoolExpression 
  | StackElement_Factor  AST.Expression 
  | StackElement_Term  AST.Expression 
  | StackElement_Expr  AST.Expression 
  | StackElement_CmdC  AST.Command 
  | StackElement_CmdO  AST.Command 
  | StackElement_Cmd  AST.Command 
  | StackElement_Instr  AST.Command 
  | StackElement_Cmds  AST.Command 
  | StackElement_Program  AST.AST 
  deriving (Show)

-- | The main parsing function. Repeatedly applies a transformation until an
--   'accept' definition is reached.
parse :: Input -> Output
parse inp = parse' ([0], [], inp)
  where
    parse' ([], [StackElement_Program result], []) = result
    parse' tuple = parse' (uncurry3 state tuple)

    uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
    uncurry3 f (a, b, c) = f a b c

-- | Reduces the given configuration (@states@, @stack@, @input@) with the given
--   rule @n@ and then performs a 'goto' to push the next state on the stack.
reduce
  :: RuleNumber                 -- ^ Rule number @n@.
  -> StateStack                 -- ^ The current state stack @states@.
  -> Stack                      -- ^ The current value stack @stack@.
  -> Input                      -- ^ The current rest of input @input@.
  -> (StateStack, Stack, Input) -- ^ The new configuration.
reduce 0 states (StackElement_Program v1 : stack) input =
  (reduceAndGoto 0 states, StackElement_Program (v1) : stack, input)
reduce 1 states (StackElement_Cmds v1 : stack) input =
  (reduceAndGoto 1 states, StackElement_Program ( v1 ) : stack, input)
reduce 2 states (StackElement_Instr v3 : _ : StackElement_Cmds v1 : stack) input =
  (reduceAndGoto 2 states, StackElement_Cmds ( AST.Sequence v1 v3 ) : stack, input)
reduce 3 states (StackElement_Instr v1 : stack) input =
  (reduceAndGoto 3 states, StackElement_Cmds ( v1 ) : stack, input)
reduce 4 states (StackElement_Cmd v1 : stack) input =
  (reduceAndGoto 4 states, StackElement_Instr ( v1 ) : stack, input)
reduce 5 states (StackElement_Alloc v1 : stack) input =
  (reduceAndGoto 5 states, StackElement_Instr ( v1 ) : stack, input)
reduce 6 states (StackElement_CmdO v1 : stack) input =
  (reduceAndGoto 6 states, StackElement_Cmd ( v1 ) : stack, input)
reduce 7 states (StackElement_CmdC v1 : stack) input =
  (reduceAndGoto 7 states, StackElement_Cmd ( v1 ) : stack, input)
reduce 8 states (stack) input =
  (reduceAndGoto 8 states, StackElement_Cmd ( AST.Skip ) : stack, input)
reduce 9 states (StackElement_Cmd v4 : _ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 9 states, StackElement_CmdO ( AST.IfThen v2 v4 ) : stack, input)
reduce 10 states (StackElement_CmdO v6 : _ : StackElement_CmdC v4 : _ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 10 states, StackElement_CmdO ( AST.IfThenElse v2 v4 v6 ) : stack, input)
reduce 11 states (StackElement_CmdO v4 : _ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 11 states, StackElement_CmdO ( AST.While v2 v4 ) : stack, input)
reduce 12 states (StackElement_CmdC v6 : _ : StackElement_CmdC v4 : _ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 12 states, StackElement_CmdC ( AST.IfThenElse v2 v4 v6 ) : stack, input)
reduce 13 states (StackElement_CmdC v4 : _ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 13 states, StackElement_CmdC ( AST.While v2 v4 ) : stack, input)
reduce 14 states (StackTerminal ( PosToken _ (Id v2) ) : _ : stack) input =
  (reduceAndGoto 14 states, StackElement_CmdC ( AST.Read v2 ) : stack, input)
reduce 15 states (StackElement_Expr v2 : _ : stack) input =
  (reduceAndGoto 15 states, StackElement_CmdC ( AST.Output v2 ) : stack, input)
reduce 16 states (StackElement_Expr v2 : _ : stack) input =
  (reduceAndGoto 16 states, StackElement_CmdC ( AST.Return v2 ) : stack, input)
reduce 17 states (StackElement_Expr v3 : _ : StackTerminal ( PosToken _ (Id v1) ) : stack) input =
  (reduceAndGoto 17 states, StackElement_CmdC ( AST.Assign v1 v3 ) : stack, input)
reduce 18 states (StackElement_Expr v6 : _ : _ : StackElement_Expr v3 : _ : StackTerminal ( PosToken _ (Id v1) ) : stack) input =
  (reduceAndGoto 18 states, StackElement_CmdC ( AST.ToArray v1 v3 v6 ) : stack, input)
reduce 19 states (_ : StackElement_Cmds v2 : _ : stack) input =
  (reduceAndGoto 19 states, StackElement_CmdC ( AST.Environment v2 ) : stack, input)
reduce 20 states (_ : StackElement_Cmds v7 : _ : _ : StackElement_Decls v4 : _ : StackElement_Decl v2 : _ : stack) input =
  (reduceAndGoto 20 states, StackElement_CmdC ( AST.Function v2 v4 v7 ) : stack, input)
reduce 21 states (StackElement_Term v3 : _ : StackElement_Expr v1 : stack) input =
  (reduceAndGoto 21 states, StackElement_Expr ( AST.Calculation Plus v1 v3 ) : stack, input)
reduce 22 states (StackElement_Term v3 : _ : StackElement_Expr v1 : stack) input =
  (reduceAndGoto 22 states, StackElement_Expr ( AST.Calculation Minus v1 v3 ) : stack, input)
reduce 23 states (StackElement_Term v1 : stack) input =
  (reduceAndGoto 23 states, StackElement_Expr ( v1 ) : stack, input)
reduce 24 states (StackElement_Factor v3 : _ : StackElement_Term v1 : stack) input =
  (reduceAndGoto 24 states, StackElement_Term ( AST.Calculation Times v1 v3 ) : stack, input)
reduce 25 states (StackElement_Factor v3 : _ : StackElement_Term v1 : stack) input =
  (reduceAndGoto 25 states, StackElement_Term ( AST.Calculation DivBy v1 v3 ) : stack, input)
reduce 26 states (StackElement_Factor v3 : _ : StackElement_Term v1 : stack) input =
  (reduceAndGoto 26 states, StackElement_Term ( AST.Calculation Mod v1 v3 ) : stack, input)
reduce 27 states (StackElement_Factor v1 : stack) input =
  (reduceAndGoto 27 states, StackElement_Term ( v1 ) : stack, input)
reduce 28 states (_ : StackElement_Expr v2 : _ : stack) input =
  (reduceAndGoto 28 states, StackElement_Factor ( v2 ) : stack, input)
reduce 29 states (StackElement_Factor v2 : _ : stack) input =
  (reduceAndGoto 29 states, StackElement_Factor ( AST.Negate v2 ) : stack, input)
reduce 30 states (StackTerminal ( PosToken _ (Id v1) ) : stack) input =
  (reduceAndGoto 30 states, StackElement_Factor ( AST.Identifier v1 ) : stack, input)
reduce 31 states (_ : StackElement_Expr v3 : _ : StackTerminal ( PosToken _ (Id v1) ) : stack) input =
  (reduceAndGoto 31 states, StackElement_Factor ( AST.FromArray v1 v3 ) : stack, input)
reduce 32 states (_ : StackElement_Params v3 : _ : StackTerminal ( PosToken _ (Id v1) ) : stack) input =
  (reduceAndGoto 32 states, StackElement_Factor ( AST.Func v1 v3 ) : stack, input)
reduce 33 states (StackTerminal ( PosToken _ (Integer v1) ) : stack) input =
  (reduceAndGoto 33 states, StackElement_Factor ( AST.Integer v1 ) : stack, input)
reduce 34 states (StackTerminal ( PosToken _ (Real v1) ) : stack) input =
  (reduceAndGoto 34 states, StackElement_Factor ( AST.Double v1 ) : stack, input)
reduce 35 states (StackTerminal ( PosToken _ (Character v1) ) : stack) input =
  (reduceAndGoto 35 states, StackElement_Factor ( AST.Character v1) : stack, input)
reduce 36 states (StackElement_Bterm v3 : _ : StackElement_Bexpr v1 : stack) input =
  (reduceAndGoto 36 states, StackElement_Bexpr ( AST.LogOp Or v1 v3 ) : stack, input)
reduce 37 states (StackElement_Bterm v1 : stack) input =
  (reduceAndGoto 37 states, StackElement_Bexpr ( v1 ) : stack, input)
reduce 38 states (StackElement_Bfactor v3 : _ : StackElement_Bterm v1 : stack) input =
  (reduceAndGoto 38 states, StackElement_Bterm ( AST.LogOp And v1 v3 ) : stack, input)
reduce 39 states (StackElement_Bfactor v1 : stack) input =
  (reduceAndGoto 39 states, StackElement_Bterm ( v1 ) : stack, input)
reduce 40 states (_ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 40 states, StackElement_Bfactor ( v2 ) : stack, input)
reduce 41 states (StackElement_Bfactor v2 : _ : stack) input =
  (reduceAndGoto 41 states, StackElement_Bfactor ( AST.Not v2 ) : stack, input)
reduce 42 states (StackElement_Expr v3 : StackTerminal ( PosToken _ (RelOp v2) ) : StackElement_Expr v1 : stack) input =
  (reduceAndGoto 42 states, StackElement_Bfactor ( AST.Comparison v2 v1 v3 ) : stack, input)
reduce 43 states (StackTerminal ( PosToken _ (Boolean v1) ) : stack) input =
  (reduceAndGoto 43 states, StackElement_Bfactor ( AST.Boolean v1 ) : stack, input)
reduce 44 states (_ : stack) input =
  (reduceAndGoto 44 states, StackElement_Bfactor ( AST.Eof ) : stack, input)
reduce 45 states (StackTerminal ( PosToken _ (Id v2) ) : _ : stack) input =
  (reduceAndGoto 45 states, StackElement_Primitives ( AST.Declaration Int v2 ) : stack, input)
reduce 46 states (StackTerminal ( PosToken _ (Id v2) ) : _ : stack) input =
  (reduceAndGoto 46 states, StackElement_Primitives ( AST.Declaration Double v2 ) : stack, input)
reduce 47 states (StackTerminal ( PosToken _ (Id v2) ) : _ : stack) input =
  (reduceAndGoto 47 states, StackElement_Primitives ( AST.Declaration Char v2) : stack, input)
reduce 48 states (StackElement_Primitives v1 : stack) input =
  (reduceAndGoto 48 states, StackElement_Alloc ( v1 ) : stack, input)
reduce 49 states (StackTerminal ( PosToken _ (Id v5) ) : _ : StackElement_Expr v3 : _ : _ : stack) input =
  (reduceAndGoto 49 states, StackElement_Alloc ( AST.ArrayAlloc Int v3 v5 ) : stack, input)
reduce 50 states (StackTerminal ( PosToken _ (Id v5) ) : _ : StackElement_Expr v3 : _ : _ : stack) input =
  (reduceAndGoto 50 states, StackElement_Alloc ( AST.ArrayAlloc Double v3 v5 ) : stack, input)
reduce 51 states (StackElement_Primitives v1 : stack) input =
  (reduceAndGoto 51 states, StackElement_Decl ( v1 ) : stack, input)
reduce 52 states (StackTerminal ( PosToken _ (Id v4) ) : _ : _ : _ : stack) input =
  (reduceAndGoto 52 states, StackElement_Decl ( AST.ArrayDecl Int v4 ) : stack, input)
reduce 53 states (StackTerminal ( PosToken _ (Id v4) ) : _ : _ : _ : stack) input =
  (reduceAndGoto 53 states, StackElement_Decl ( AST.ArrayDecl Double v4 ) : stack, input)
reduce 54 states (StackElement_Decl v3 : _ : StackElement_Decls v1 : stack) input =
  (reduceAndGoto 54 states, StackElement_Decls ( AST.Sequence v1 v3 ) : stack, input)
reduce 55 states (StackElement_Decl v1 : stack) input =
  (reduceAndGoto 55 states, StackElement_Decls ( v1 ) : stack, input)
reduce 56 states (StackElement_Param v3 : _ : StackElement_Params v1 : stack) input =
  (reduceAndGoto 56 states, StackElement_Params ( AST.Parameters v1 v3 ) : stack, input)
reduce 57 states (StackElement_Param v1 : stack) input =
  (reduceAndGoto 57 states, StackElement_Params ( v1 ) : stack, input)
reduce 58 states (StackElement_Expr v1 : stack) input =
  (reduceAndGoto 58 states, StackElement_Param ( AST.Parameter v1 ) : stack, input)

reduce n states stack input = error $
  "Reached a non-defined reduce.\nRule: " ++ show n ++ "\nStates: " ++
  show states ++ "\nStack: " ++ show stack ++ "\nInput: " ++ show input

-- | A helper function used by 'reduce' which pops the correct number of states
--   from the stack and performs a 'goto' to push the next state on the stack.
reduceAndGoto
  :: RuleNumber
  -> StateStack
  -> StateStack
reduceAndGoto rule states = newState : states'
  where
    states' = drop (reduceNumber rule) states
    newState = goto (head states') (lhs rule)

-- | Returns the number of states to be popped from the stack for a given rule.
reduceNumber
  :: RuleNumber
  -> Int
reduceNumber = (reduceList !!)
  where
    reduceList :: [Int]
    reduceList = [1,1,3,1,1,1,1,1,0,4,6,4,6,4,2,2,2,3,6,3,8,3,3,1,3,3,3,1,3,2,1,4,4,1,1,1,3,1,3,1,3,2,3,1,1,2,2,2,1,5,5,1,4,4,3,1,3,1,1]

-- | Returns the number of the non-terminal symbol for a given rule.
lhs
  :: RuleNumber
  -> NonTerminal
lhs = (lhsList !!)
  where
    lhsList :: [NonTerminal]
    lhsList = [0,1,2,2,3,3,4,4,4,5,5,5,6,6,6,6,6,6,6,6,6,7,7,7,8,8,8,8,9,9,9,9,9,9,9,9,10,10,11,11,12,12,12,12,12,13,13,13,14,14,14,15,15,15,16,16,17,17,18]

-- | For a given state and non-terminal symbol returns the next state we will
--   enter.
goto
  :: State
  -> NonTerminal
  -> State
goto 0 1 = 12
goto 0 2 = 13
goto 0 3 = 14
goto 0 4 = 15
goto 0 5 = 16
goto 0 6 = 17
goto 0 13 = 18
goto 0 14 = 19
goto 3 7 = 29
goto 3 8 = 30
goto 3 9 = 31
goto 4 7 = 32
goto 4 8 = 30
goto 4 9 = 31
goto 5 7 = 37
goto 5 8 = 30
goto 5 9 = 31
goto 5 10 = 38
goto 5 11 = 39
goto 5 12 = 40
goto 6 7 = 37
goto 6 8 = 30
goto 6 9 = 31
goto 6 10 = 41
goto 6 11 = 39
goto 6 12 = 40
goto 10 13 = 49
goto 10 15 = 50
goto 11 2 = 51
goto 11 3 = 14
goto 11 4 = 15
goto 11 5 = 16
goto 11 6 = 17
goto 11 13 = 18
goto 11 14 = 19
goto 20 7 = 53
goto 20 8 = 30
goto 20 9 = 31
goto 21 7 = 54
goto 21 8 = 30
goto 21 9 = 31
goto 27 9 = 57
goto 28 7 = 58
goto 28 8 = 30
goto 28 9 = 31
goto 34 7 = 37
goto 34 8 = 30
goto 34 9 = 31
goto 34 12 = 64
goto 36 7 = 65
goto 36 8 = 30
goto 36 9 = 31
goto 36 10 = 66
goto 36 11 = 39
goto 36 12 = 40
goto 43 7 = 72
goto 43 8 = 30
goto 43 9 = 31
goto 45 7 = 73
goto 45 8 = 30
goto 45 9 = 31
goto 52 3 = 78
goto 52 4 = 15
goto 52 5 = 16
goto 52 6 = 17
goto 52 13 = 18
goto 52 14 = 19
goto 55 7 = 80
goto 55 8 = 30
goto 55 9 = 31
goto 55 17 = 81
goto 55 18 = 82
goto 56 7 = 83
goto 56 8 = 30
goto 56 9 = 31
goto 59 8 = 85
goto 59 9 = 31
goto 60 8 = 86
goto 60 9 = 31
goto 61 9 = 87
goto 62 9 = 88
goto 63 9 = 89
goto 67 7 = 91
goto 67 8 = 30
goto 67 9 = 31
goto 68 7 = 37
goto 68 8 = 30
goto 68 9 = 31
goto 68 11 = 92
goto 68 12 = 40
goto 69 4 = 93
goto 69 5 = 16
goto 69 6 = 94
goto 70 7 = 37
goto 70 8 = 30
goto 70 9 = 31
goto 70 12 = 95
goto 71 5 = 96
goto 71 6 = 97
goto 76 13 = 49
goto 76 15 = 102
goto 76 16 = 103
goto 104 7 = 115
goto 104 8 = 30
goto 104 9 = 31
goto 106 7 = 80
goto 106 8 = 30
goto 106 9 = 31
goto 106 18 = 116
goto 108 5 = 117
goto 108 6 = 118
goto 114 13 = 49
goto 114 15 = 120
goto 119 2 = 121
goto 119 3 = 14
goto 119 4 = 15
goto 119 5 = 16
goto 119 6 = 17
goto 119 13 = 18
goto 119 14 = 19

goto state_ nonterminal = error $
  "Reached a non-defined goto.\nState: " ++ show state_ ++ "\nNon-Terminal: " ++
  show nonterminal

-- | Pushes the given state on the state stack, pushes the first input symbol on
--   the value stack and removes it from the input.
shift
  :: State
  -> StateStack
  -> Stack
  -> Input
  -> (StateStack, Stack, Input)
shift state_ states stack input =
  (state_ : states, StackTerminal (head input) : stack, tail input)

-- | Accepts an input. This is only possible for an empty input and if both
--   stacks contain exactly one element. We then remove the last state from the
--   state stack.
accept
  :: StateStack
  -> Stack
  -> Input
  -> (StateStack, Stack, Input)
accept (_:_:[]) stack@(_:[]) [] = ([], stack, [])
accept states stack input = error $
  "Reached accept with a non-singleton stack.\nStates: " ++ show states ++
  "\nStack: " ++ show stack ++ "\nInput: " ++ show input

-- | Here all the transformations are handled. Depending on the next input
--   symbol a 'shift', 'reduce', 'accept' or error is triggered.
state
  :: StateStack
  -> Stack
  -> Input
  -> (StateStack, Stack, Input)
state states@(0:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _  Read ) -> shift 2 states stack input
  Just ( PosToken _  Output ) -> shift 3 states stack input
  Just ( PosToken _  Return ) -> shift 4 states stack input
  Just ( PosToken _  If ) -> shift 5 states stack input
  Just ( PosToken _  While ) -> shift 6 states stack input
  Just ( PosToken _ (Type Int) ) -> shift 7 states stack input
  Just ( PosToken _ (Type Double) ) -> shift 8 states stack input
  Just ( PosToken _ (Type Char) ) -> shift 9 states stack input
  Just ( PosToken _  Function ) -> shift 10 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 11 states stack input
  Nothing -> reduce 8 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 8 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 8 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, read, output, return, if, while, int, double, char, func, '{', 'eof', ';', '}'"
state states@(1:_) stack input = case headMay input of
  Just ( PosToken _  Assign ) -> shift 20 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 21 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ':=', '['"
state states@(2:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 22 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(3:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(4:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(5:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Boolean _) ) -> shift 33 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _  Not ) -> shift 34 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _  Eof ) -> shift 35 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 36 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, '-', eof, '('"
state states@(6:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Boolean _) ) -> shift 33 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _  Not ) -> shift 34 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _  Eof ) -> shift 35 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 36 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, '-', eof, '('"
state states@(7:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 42 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 43 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, '['"
state states@(8:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 44 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 45 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, '['"
state states@(9:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 46 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(10:_) stack input = case headMay input of
  Just ( PosToken _ (Type Int) ) -> shift 47 states stack input
  Just ( PosToken _ (Type Double) ) -> shift 48 states stack input
  Just ( PosToken _ (Type Char) ) -> shift 9 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting int, double, char"
state states@(11:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _  Read ) -> shift 2 states stack input
  Just ( PosToken _  Output ) -> shift 3 states stack input
  Just ( PosToken _  Return ) -> shift 4 states stack input
  Just ( PosToken _  If ) -> shift 5 states stack input
  Just ( PosToken _  While ) -> shift 6 states stack input
  Just ( PosToken _ (Type Int) ) -> shift 7 states stack input
  Just ( PosToken _ (Type Double) ) -> shift 8 states stack input
  Just ( PosToken _ (Type Char) ) -> shift 9 states stack input
  Just ( PosToken _  Function ) -> shift 10 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 11 states stack input
  Nothing -> reduce 8 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 8 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 8 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, read, output, return, if, while, int, double, char, func, '{', 'eof', ';', '}'"
state states@(12:_) stack input = case headMay input of
  Nothing -> accept states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof'"
state states@(13:_) stack input = case headMay input of
  Just ( PosToken _ (Token ';') ) -> shift 52 states stack input
  Nothing -> reduce 1 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ';', 'eof'"
state states@(14:_) stack input = case headMay input of
  Nothing -> reduce 3 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 3 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 3 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(15:_) stack input = case headMay input of
  Nothing -> reduce 4 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 4 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 4 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(16:_) stack input = case headMay input of
  Nothing -> reduce 6 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 6 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 6 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(17:_) stack input = case headMay input of
  Nothing -> reduce 7 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 7 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 7 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(18:_) stack input = case headMay input of
  Nothing -> reduce 48 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 48 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 48 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(19:_) stack input = case headMay input of
  Nothing -> reduce 5 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 5 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 5 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(20:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(21:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(22:_) stack input = case headMay input of
  Nothing -> reduce 14 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 14 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 14 states stack input
  Just ( PosToken _  Else ) -> reduce 14 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}', else"
state states@(23:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> shift 55 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 56 states stack input
  Nothing -> reduce 30 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 30 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 30 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 30 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 30 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 30 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 30 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 30 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 30 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 30 states stack input
  Just ( PosToken _  Do ) -> reduce 30 states stack input
  Just ( PosToken _  Else ) -> reduce 30 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 30 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 30 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 30 states stack input
  Just ( PosToken _  Then ) -> reduce 30 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', '[', 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(24:_) stack input = case headMay input of
  Nothing -> reduce 33 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 33 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 33 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 33 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 33 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 33 states stack input
  Just ( PosToken _  Do ) -> reduce 33 states stack input
  Just ( PosToken _  Else ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 33 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 33 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 33 states stack input
  Just ( PosToken _  Then ) -> reduce 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(25:_) stack input = case headMay input of
  Nothing -> reduce 34 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 34 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 34 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 34 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 34 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 34 states stack input
  Just ( PosToken _  Do ) -> reduce 34 states stack input
  Just ( PosToken _  Else ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 34 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 34 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 34 states stack input
  Just ( PosToken _  Then ) -> reduce 34 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(26:_) stack input = case headMay input of
  Nothing -> reduce 35 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 35 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 35 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 35 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 35 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 35 states stack input
  Just ( PosToken _  Do ) -> reduce 35 states stack input
  Just ( PosToken _  Else ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 35 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 35 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 35 states stack input
  Just ( PosToken _  Then ) -> reduce 35 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(27:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(28:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(29:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Nothing -> reduce 15 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 15 states stack input
  Just ( PosToken _  Else ) -> reduce 15 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', 'eof', ';', '}', else"
state states@(30:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Times) ) -> shift 61 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> shift 62 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> shift 63 states stack input
  Nothing -> reduce 23 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 23 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 23 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 23 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 23 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 23 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 23 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 23 states stack input
  Just ( PosToken _  Do ) -> reduce 23 states stack input
  Just ( PosToken _  Else ) -> reduce 23 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 23 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 23 states stack input
  Just ( PosToken _  Then ) -> reduce 23 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '*', '/', mod, 'eof', ')', '+', '-', ';', ']', '}', and, do, else, or, relop, then"
state states@(31:_) stack input = case headMay input of
  Nothing -> reduce 27 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 27 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 27 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 27 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 27 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 27 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 27 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 27 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 27 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 27 states stack input
  Just ( PosToken _  Do ) -> reduce 27 states stack input
  Just ( PosToken _  Else ) -> reduce 27 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 27 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 27 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 27 states stack input
  Just ( PosToken _  Then ) -> reduce 27 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(32:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Nothing -> reduce 16 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 16 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 16 states stack input
  Just ( PosToken _  Else ) -> reduce 16 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', 'eof', ';', '}', else"
state states@(33:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 43 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 43 states stack input
  Just ( PosToken _  Do ) -> reduce 43 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 43 states stack input
  Just ( PosToken _  Then ) -> reduce 43 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(34:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Boolean _) ) -> shift 33 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _  Not ) -> shift 34 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _  Eof ) -> shift 35 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 36 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, '-', eof, '('"
state states@(35:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 44 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 44 states stack input
  Just ( PosToken _  Do ) -> reduce 44 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 44 states stack input
  Just ( PosToken _  Then ) -> reduce 44 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(36:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Boolean _) ) -> shift 33 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _  Not ) -> shift 34 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _  Eof ) -> shift 35 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 36 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, '-', eof, '('"
state states@(37:_) stack input = case headMay input of
  Just ( PosToken _ (RelOp _) ) -> shift 67 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting relop, '+', '-'"
state states@(38:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp Or) ) -> shift 68 states stack input
  Just ( PosToken _  Then ) -> shift 69 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting or, then"
state states@(39:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp And) ) -> shift 70 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 37 states stack input
  Just ( PosToken _  Do ) -> reduce 37 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 37 states stack input
  Just ( PosToken _  Then ) -> reduce 37 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting and, ')', do, or, then"
state states@(40:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 39 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 39 states stack input
  Just ( PosToken _  Do ) -> reduce 39 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 39 states stack input
  Just ( PosToken _  Then ) -> reduce 39 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(41:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp Or) ) -> shift 68 states stack input
  Just ( PosToken _  Do ) -> shift 71 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting or, do"
state states@(42:_) stack input = case headMay input of
  Nothing -> reduce 45 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 45 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 45 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 45 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 45 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', '(', ')', ';', '}'"
state states@(43:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(44:_) stack input = case headMay input of
  Nothing -> reduce 46 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 46 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 46 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 46 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 46 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', '(', ')', ';', '}'"
state states@(45:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(46:_) stack input = case headMay input of
  Nothing -> reduce 47 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 47 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 47 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 47 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 47 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', '(', ')', ';', '}'"
state states@(47:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 42 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 74 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, '['"
state states@(48:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 44 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 75 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, '['"
state states@(49:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> reduce 51 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 51 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 51 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', ')', ';'"
state states@(50:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> shift 76 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '('"
state states@(51:_) stack input = case headMay input of
  Just ( PosToken _ (Token '}') ) -> shift 77 states stack input
  Just ( PosToken _ (Token ';') ) -> shift 52 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '}', ';'"
state states@(52:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _  Read ) -> shift 2 states stack input
  Just ( PosToken _  Output ) -> shift 3 states stack input
  Just ( PosToken _  Return ) -> shift 4 states stack input
  Just ( PosToken _  If ) -> shift 5 states stack input
  Just ( PosToken _  While ) -> shift 6 states stack input
  Just ( PosToken _ (Type Int) ) -> shift 7 states stack input
  Just ( PosToken _ (Type Double) ) -> shift 8 states stack input
  Just ( PosToken _ (Type Char) ) -> shift 9 states stack input
  Just ( PosToken _  Function ) -> shift 10 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 11 states stack input
  Nothing -> reduce 8 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 8 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 8 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, read, output, return, if, while, int, double, char, func, '{', 'eof', ';', '}'"
state states@(53:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Nothing -> reduce 17 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 17 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 17 states stack input
  Just ( PosToken _  Else ) -> reduce 17 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', 'eof', ';', '}', else"
state states@(54:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Just ( PosToken _ (Token ']') ) -> shift 79 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ']'"
state states@(55:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(56:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(57:_) stack input = case headMay input of
  Nothing -> reduce 29 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 29 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 29 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 29 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 29 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 29 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 29 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 29 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 29 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 29 states stack input
  Just ( PosToken _  Do ) -> reduce 29 states stack input
  Just ( PosToken _  Else ) -> reduce 29 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 29 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 29 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 29 states stack input
  Just ( PosToken _  Then ) -> reduce 29 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(58:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Just ( PosToken _ (Token ')') ) -> shift 84 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ')'"
state states@(59:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(60:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(61:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(62:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(63:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(64:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 41 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 41 states stack input
  Just ( PosToken _  Do ) -> reduce 41 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 41 states stack input
  Just ( PosToken _  Then ) -> reduce 41 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(65:_) stack input = case headMay input of
  Just ( PosToken _ (RelOp _) ) -> shift 67 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Just ( PosToken _ (Token ')') ) -> shift 84 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting relop, '+', '-', ')'"
state states@(66:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp Or) ) -> shift 68 states stack input
  Just ( PosToken _ (Token ')') ) -> shift 90 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting or, ')'"
state states@(67:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(68:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Boolean _) ) -> shift 33 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _  Not ) -> shift 34 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _  Eof ) -> shift 35 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 36 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, '-', eof, '('"
state states@(69:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _  Read ) -> shift 2 states stack input
  Just ( PosToken _  Output ) -> shift 3 states stack input
  Just ( PosToken _  Return ) -> shift 4 states stack input
  Just ( PosToken _  If ) -> shift 5 states stack input
  Just ( PosToken _  While ) -> shift 6 states stack input
  Just ( PosToken _  Function ) -> shift 10 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 11 states stack input
  Nothing -> reduce 8 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 8 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 8 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, read, output, return, if, while, func, '{', 'eof', ';', '}'"
state states@(70:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Boolean _) ) -> shift 33 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _  Not ) -> shift 34 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _  Eof ) -> shift 35 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 36 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, '-', eof, '('"
state states@(71:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _  Read ) -> shift 2 states stack input
  Just ( PosToken _  Output ) -> shift 3 states stack input
  Just ( PosToken _  Return ) -> shift 4 states stack input
  Just ( PosToken _  If ) -> shift 5 states stack input
  Just ( PosToken _  While ) -> shift 6 states stack input
  Just ( PosToken _  Function ) -> shift 10 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 11 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, read, output, return, if, while, func, '{'"
state states@(72:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Just ( PosToken _ (Token ']') ) -> shift 98 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ']'"
state states@(73:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Just ( PosToken _ (Token ']') ) -> shift 99 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ']'"
state states@(74:_) stack input = case headMay input of
  Just ( PosToken _ (Token ']') ) -> shift 100 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ']'"
state states@(75:_) stack input = case headMay input of
  Just ( PosToken _ (Token ']') ) -> shift 101 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ']'"
state states@(76:_) stack input = case headMay input of
  Just ( PosToken _ (Type Int) ) -> shift 47 states stack input
  Just ( PosToken _ (Type Double) ) -> shift 48 states stack input
  Just ( PosToken _ (Type Char) ) -> shift 9 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting int, double, char"
state states@(77:_) stack input = case headMay input of
  Nothing -> reduce 19 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 19 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 19 states stack input
  Just ( PosToken _  Else ) -> reduce 19 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}', else"
state states@(78:_) stack input = case headMay input of
  Nothing -> reduce 2 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 2 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 2 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(79:_) stack input = case headMay input of
  Just ( PosToken _  Assign ) -> shift 104 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ':='"
state states@(80:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 58 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 58 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ')', ';'"
state states@(81:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> shift 105 states stack input
  Just ( PosToken _ (Token ';') ) -> shift 106 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(82:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 57 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 57 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(83:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Just ( PosToken _ (Token ']') ) -> shift 107 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ']'"
state states@(84:_) stack input = case headMay input of
  Nothing -> reduce 28 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 28 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 28 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 28 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 28 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 28 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 28 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 28 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 28 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 28 states stack input
  Just ( PosToken _  Do ) -> reduce 28 states stack input
  Just ( PosToken _  Else ) -> reduce 28 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 28 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 28 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 28 states stack input
  Just ( PosToken _  Then ) -> reduce 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(85:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Times) ) -> shift 61 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> shift 62 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> shift 63 states stack input
  Nothing -> reduce 21 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 21 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 21 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 21 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 21 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 21 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 21 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 21 states stack input
  Just ( PosToken _  Do ) -> reduce 21 states stack input
  Just ( PosToken _  Else ) -> reduce 21 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 21 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 21 states stack input
  Just ( PosToken _  Then ) -> reduce 21 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '*', '/', mod, 'eof', ')', '+', '-', ';', ']', '}', and, do, else, or, relop, then"
state states@(86:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Times) ) -> shift 61 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> shift 62 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> shift 63 states stack input
  Nothing -> reduce 22 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 22 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 22 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 22 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 22 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 22 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 22 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 22 states stack input
  Just ( PosToken _  Do ) -> reduce 22 states stack input
  Just ( PosToken _  Else ) -> reduce 22 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 22 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 22 states stack input
  Just ( PosToken _  Then ) -> reduce 22 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '*', '/', mod, 'eof', ')', '+', '-', ';', ']', '}', and, do, else, or, relop, then"
state states@(87:_) stack input = case headMay input of
  Nothing -> reduce 24 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 24 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 24 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 24 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 24 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 24 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 24 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 24 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 24 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 24 states stack input
  Just ( PosToken _  Do ) -> reduce 24 states stack input
  Just ( PosToken _  Else ) -> reduce 24 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 24 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 24 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 24 states stack input
  Just ( PosToken _  Then ) -> reduce 24 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(88:_) stack input = case headMay input of
  Nothing -> reduce 25 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 25 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 25 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 25 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 25 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 25 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 25 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 25 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 25 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 25 states stack input
  Just ( PosToken _  Do ) -> reduce 25 states stack input
  Just ( PosToken _  Else ) -> reduce 25 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 25 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 25 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 25 states stack input
  Just ( PosToken _  Then ) -> reduce 25 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(89:_) stack input = case headMay input of
  Nothing -> reduce 26 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 26 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 26 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 26 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 26 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 26 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 26 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 26 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 26 states stack input
  Just ( PosToken _  Do ) -> reduce 26 states stack input
  Just ( PosToken _  Else ) -> reduce 26 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 26 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 26 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 26 states stack input
  Just ( PosToken _  Then ) -> reduce 26 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(90:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 40 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 40 states stack input
  Just ( PosToken _  Do ) -> reduce 40 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 40 states stack input
  Just ( PosToken _  Then ) -> reduce 40 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(91:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 42 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 42 states stack input
  Just ( PosToken _  Do ) -> reduce 42 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 42 states stack input
  Just ( PosToken _  Then ) -> reduce 42 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ')', and, do, or, then"
state states@(92:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp And) ) -> shift 70 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 36 states stack input
  Just ( PosToken _  Do ) -> reduce 36 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 36 states stack input
  Just ( PosToken _  Then ) -> reduce 36 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting and, ')', do, or, then"
state states@(93:_) stack input = case headMay input of
  Nothing -> reduce 9 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 9 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 9 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(94:_) stack input = case headMay input of
  Just ( PosToken _  Else ) -> shift 108 states stack input
  Nothing -> reduce 7 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 7 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 7 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting else, 'eof', ';', '}'"
state states@(95:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 38 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 38 states stack input
  Just ( PosToken _  Do ) -> reduce 38 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 38 states stack input
  Just ( PosToken _  Then ) -> reduce 38 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(96:_) stack input = case headMay input of
  Nothing -> reduce 11 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 11 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 11 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(97:_) stack input = case headMay input of
  Nothing -> reduce 13 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 13 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 13 states stack input
  Just ( PosToken _  Else ) -> reduce 13 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}', else"
state states@(98:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 109 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(99:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 110 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(100:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 111 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(101:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 112 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(102:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 55 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 55 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(103:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> shift 113 states stack input
  Just ( PosToken _ (Token ';') ) -> shift 114 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(104:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(105:_) stack input = case headMay input of
  Nothing -> reduce 32 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 32 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 32 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 32 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 32 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 32 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 32 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 32 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 32 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 32 states stack input
  Just ( PosToken _  Do ) -> reduce 32 states stack input
  Just ( PosToken _  Else ) -> reduce 32 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 32 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 32 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 32 states stack input
  Just ( PosToken _  Then ) -> reduce 32 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(106:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 23 states stack input
  Just ( PosToken _ (Integer _) ) -> shift 24 states stack input
  Just ( PosToken _ (Real _) ) -> shift 25 states stack input
  Just ( PosToken _ (Character _) ) -> shift 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 27 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 28 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, '-', '('"
state states@(107:_) stack input = case headMay input of
  Nothing -> reduce 31 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 31 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 31 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 31 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 31 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 31 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 31 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 31 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 31 states stack input
  Just ( PosToken _  Do ) -> reduce 31 states stack input
  Just ( PosToken _  Else ) -> reduce 31 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 31 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 31 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 31 states stack input
  Just ( PosToken _  Then ) -> reduce 31 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(108:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _  Read ) -> shift 2 states stack input
  Just ( PosToken _  Output ) -> shift 3 states stack input
  Just ( PosToken _  Return ) -> shift 4 states stack input
  Just ( PosToken _  If ) -> shift 5 states stack input
  Just ( PosToken _  While ) -> shift 6 states stack input
  Just ( PosToken _  Function ) -> shift 10 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 11 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, read, output, return, if, while, func, '{'"
state states@(109:_) stack input = case headMay input of
  Nothing -> reduce 49 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 49 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 49 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(110:_) stack input = case headMay input of
  Nothing -> reduce 50 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 50 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 50 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(111:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> reduce 52 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 52 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 52 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', ')', ';'"
state states@(112:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> reduce 53 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 53 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 53 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', ')', ';'"
state states@(113:_) stack input = case headMay input of
  Just ( PosToken _ (Token '{') ) -> shift 119 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '{'"
state states@(114:_) stack input = case headMay input of
  Just ( PosToken _ (Type Int) ) -> shift 47 states stack input
  Just ( PosToken _ (Type Double) ) -> shift 48 states stack input
  Just ( PosToken _ (Type Char) ) -> shift 9 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting int, double, char"
state states@(115:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 59 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 60 states stack input
  Nothing -> reduce 18 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 18 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 18 states stack input
  Just ( PosToken _  Else ) -> reduce 18 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', 'eof', ';', '}', else"
state states@(116:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 56 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 56 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(117:_) stack input = case headMay input of
  Nothing -> reduce 10 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 10 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 10 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(118:_) stack input = case headMay input of
  Nothing -> reduce 12 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 12 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 12 states stack input
  Just ( PosToken _  Else ) -> reduce 12 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}', else"
state states@(119:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _  Read ) -> shift 2 states stack input
  Just ( PosToken _  Output ) -> shift 3 states stack input
  Just ( PosToken _  Return ) -> shift 4 states stack input
  Just ( PosToken _  If ) -> shift 5 states stack input
  Just ( PosToken _  While ) -> shift 6 states stack input
  Just ( PosToken _ (Type Int) ) -> shift 7 states stack input
  Just ( PosToken _ (Type Double) ) -> shift 8 states stack input
  Just ( PosToken _ (Type Char) ) -> shift 9 states stack input
  Just ( PosToken _  Function ) -> shift 10 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 11 states stack input
  Nothing -> reduce 8 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 8 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 8 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, read, output, return, if, while, int, double, char, func, '{', 'eof', ';', '}'"
state states@(120:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 54 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 54 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(121:_) stack input = case headMay input of
  Just ( PosToken _ (Token '}') ) -> shift 122 states stack input
  Just ( PosToken _ (Token ';') ) -> shift 52 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '}', ';'"
state states@(122:_) stack input = case headMay input of
  Nothing -> reduce 20 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 20 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 20 states stack input
  Just ( PosToken _  Else ) -> reduce 20 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}', else"

state states stack input = error $
  "Reached a non-defined state.\nStates: " ++ show states ++ "\nStack: " ++
  show stack ++ "\nInput: " ++ show input
