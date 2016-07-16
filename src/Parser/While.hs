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
  | StackElement_Bfactor  AST.BoolExpression 
  | StackElement_Bterm  AST.BoolExpression 
  | StackElement_Bexpr  AST.BoolExpression 
  | StackElement_Types  Type 
  | StackElement_Type  Type 
  | StackElement_Decls  AST.Command 
  | StackElement_Decl  AST.Command 
  | StackElement_Param  AST.Expression 
  | StackElement_Params  AST.Expression 
  | StackElement_Element  AST.Address 
  | StackElement_Elements  AST.Address 
  | StackElement_Addr  AST.Address 
  | StackElement_Factor  AST.Expression 
  | StackElement_Term  AST.Expression 
  | StackElement_Expr  AST.Expression 
  | StackElement_Instr  AST.Command 
  | StackElement_Cmd  AST.Command 
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
reduce 2 states (StackElement_Cmd v3 : _ : StackElement_Cmds v1 : stack) input =
  (reduceAndGoto 2 states, StackElement_Cmds ( AST.Sequence v1 v3 ) : stack, input)
reduce 3 states (StackElement_Cmd v1 : stack) input =
  (reduceAndGoto 3 states, StackElement_Cmds ( v1 ) : stack, input)
reduce 4 states (_ : StackElement_Cmds v2 : _ : stack) input =
  (reduceAndGoto 4 states, StackElement_Cmd ( AST.Environment v2 ) : stack, input)
reduce 5 states (StackElement_Cmd v4 : _ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 5 states, StackElement_Cmd ( AST.IfThen v2 v4 ) : stack, input)
reduce 6 states (StackElement_Cmd v6 : _ : StackElement_Cmd v4 : _ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 6 states, StackElement_Cmd ( AST.IfThenElse v2 v4 v6 ) : stack, input)
reduce 7 states (StackElement_Cmd v4 : _ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 7 states, StackElement_Cmd ( AST.While v2 v4 ) : stack, input)
reduce 8 states (StackElement_Instr v1 : stack) input =
  (reduceAndGoto 8 states, StackElement_Cmd ( v1 ) : stack, input)
reduce 9 states (StackElement_Expr v3 : _ : StackElement_Addr v1 : stack) input =
  (reduceAndGoto 9 states, StackElement_Instr ( AST.Assign v1 v3 ) : stack, input)
reduce 10 states (StackElement_Addr v5 : _ : StackElement_Expr v3 : _ : StackElement_Type v1 : stack) input =
  (reduceAndGoto 10 states, StackElement_Instr ( AST.ArrayAlloc v1 v3 v5 ) : stack, input)
reduce 11 states (StackElement_Expr v2 : _ : stack) input =
  (reduceAndGoto 11 states, StackElement_Instr ( AST.Output v2 ) : stack, input)
reduce 12 states (StackElement_Addr v2 : _ : stack) input =
  (reduceAndGoto 12 states, StackElement_Instr ( AST.Read v2 ) : stack, input)
reduce 13 states (StackElement_Expr v2 : _ : stack) input =
  (reduceAndGoto 13 states, StackElement_Instr ( AST.Return v2 ) : stack, input)
reduce 14 states (StackElement_Decl v1 : stack) input =
  (reduceAndGoto 14 states, StackElement_Instr ( v1 ) : stack, input)
reduce 15 states (stack) input =
  (reduceAndGoto 15 states, StackElement_Instr ( AST.Skip ) : stack, input)
reduce 16 states (StackElement_Term v3 : _ : StackElement_Expr v1 : stack) input =
  (reduceAndGoto 16 states, StackElement_Expr ( AST.Calculation Plus v1 v3 ) : stack, input)
reduce 17 states (StackElement_Term v3 : _ : StackElement_Expr v1 : stack) input =
  (reduceAndGoto 17 states, StackElement_Expr ( AST.Calculation Minus v1 v3) : stack, input)
reduce 18 states (StackElement_Term v1 : stack) input =
  (reduceAndGoto 18 states, StackElement_Expr ( v1 ) : stack, input)
reduce 19 states (StackElement_Factor v3 : _ : StackElement_Term v1 : stack) input =
  (reduceAndGoto 19 states, StackElement_Term ( AST.Calculation Times v1 v3 ) : stack, input)
reduce 20 states (StackElement_Factor v3 : _ : StackElement_Term v1 : stack) input =
  (reduceAndGoto 20 states, StackElement_Term ( AST.Calculation DivBy v1 v3 ) : stack, input)
reduce 21 states (StackElement_Factor v3 : _ : StackElement_Term v1 : stack) input =
  (reduceAndGoto 21 states, StackElement_Term ( AST.Calculation Mod v1 v3 ) : stack, input)
reduce 22 states (StackElement_Factor v1 : stack) input =
  (reduceAndGoto 22 states, StackElement_Term ( v1 ) : stack, input)
reduce 23 states (StackTerminal ( PosToken _ (Id v2) ) : _ : stack) input =
  (reduceAndGoto 23 states, StackElement_Factor ( AST.ToClass v2 ) : stack, input)
reduce 24 states (StackElement_Factor v2 : _ : stack) input =
  (reduceAndGoto 24 states, StackElement_Factor ( AST.Negate v2 ) : stack, input)
reduce 25 states (StackElement_Param v1 : stack) input =
  (reduceAndGoto 25 states, StackElement_Factor ( v1 ) : stack, input)
reduce 26 states (StackElement_Elements v3 : _ : StackTerminal ( PosToken _ (Id v1) ) : stack) input =
  (reduceAndGoto 26 states, StackElement_Addr ( AST.Structure ( AST.Identifier v1 ) v3 ) : stack, input)
reduce 27 states (StackElement_Element v1 : stack) input =
  (reduceAndGoto 27 states, StackElement_Addr ( v1) : stack, input)
reduce 28 states (StackElement_Element v3 : _ : StackElement_Elements v1 : stack) input =
  (reduceAndGoto 28 states, StackElement_Elements ( AST.Structure v1 v3 ) : stack, input)
reduce 29 states (StackElement_Element v1 : stack) input =
  (reduceAndGoto 29 states, StackElement_Elements ( v1 ) : stack, input)
reduce 30 states (_ : StackElement_Expr v3 : _ : StackElement_Element v1 : stack) input =
  (reduceAndGoto 30 states, StackElement_Element ( AST.FromArray v1 v3 ) : stack, input)
reduce 31 states (_ : StackElement_Params v3 : _ : StackElement_Element v1 : stack) input =
  (reduceAndGoto 31 states, StackElement_Element ( AST.FunctionCall v1 v3 ) : stack, input)
reduce 32 states (_ : _ : StackElement_Element v1 : stack) input =
  (reduceAndGoto 32 states, StackElement_Element ( AST.FunctionCall v1 AST.Void ) : stack, input)
reduce 33 states (StackTerminal ( PosToken _ (Id v3) ) : _ : StackTerminal ( PosToken _ (Id v1) ) : stack) input =
  (reduceAndGoto 33 states, StackElement_Element ( AST.Label v1 v3 ) : stack, input)
reduce 34 states (StackTerminal ( PosToken _ (Id v2) ) : _ : stack) input =
  (reduceAndGoto 34 states, StackElement_Element ( AST.Label "default" v2 ) : stack, input)
reduce 35 states (StackTerminal ( PosToken _ (Id v1) ) : stack) input =
  (reduceAndGoto 35 states, StackElement_Element ( AST.Identifier v1 ) : stack, input)
reduce 36 states (StackElement_Param v3 : _ : StackElement_Params v1 : stack) input =
  (reduceAndGoto 36 states, StackElement_Params ( AST.Parameters v1 v3 ) : stack, input)
reduce 37 states (StackElement_Param v1 : stack) input =
  (reduceAndGoto 37 states, StackElement_Params ( v1 ) : stack, input)
reduce 38 states (StackTerminal ( PosToken _ (DInt v1) ) : stack) input =
  (reduceAndGoto 38 states, StackElement_Param ( AST.Integer v1 ) : stack, input)
reduce 39 states (StackTerminal ( PosToken _ (DDouble v1) ) : stack) input =
  (reduceAndGoto 39 states, StackElement_Param ( AST.Double v1 ) : stack, input)
reduce 40 states (StackTerminal ( PosToken _ (DChar v1) ) : stack) input =
  (reduceAndGoto 40 states, StackElement_Param ( AST.Character v1 ) : stack, input)
reduce 41 states (StackTerminal ( PosToken _ (Id v3) ) : _ : StackTerminal ( PosToken _ (Id v1) ) : stack) input =
  (reduceAndGoto 41 states, StackElement_Param ( AST.Reference v1 v3 ) : stack, input)
reduce 42 states (StackTerminal ( PosToken _ (Id v2) ) : _ : stack) input =
  (reduceAndGoto 42 states, StackElement_Param ( AST.Reference "default" v2 ) : stack, input)
reduce 43 states (StackElement_Addr v1 : stack) input =
  (reduceAndGoto 43 states, StackElement_Param ( AST.Variable v1 ) : stack, input)
reduce 44 states (StackElement_Cmd v7 : _ : StackElement_Decls v5 : _ : StackTerminal ( PosToken _ (Id v3) ) : StackElement_Type v2 : _ : stack) input =
  (reduceAndGoto 44 states, StackElement_Decl ( AST.Function v2 v3 v5 v7 ) : stack, input)
reduce 45 states (_ : StackElement_Decls v4 : _ : StackTerminal ( PosToken _ (Id v2) ) : _ : stack) input =
  (reduceAndGoto 45 states, StackElement_Decl ( AST.LabelEnvironment v2 v4 ) : stack, input)
reduce 46 states (StackTerminal ( PosToken _ (Id v2) ) : StackElement_Type v1 : stack) input =
  (reduceAndGoto 46 states, StackElement_Decl ( AST.Declaration v1 v2 ) : stack, input)
reduce 47 states (StackElement_Decl v3 : _ : StackElement_Decls v1 : stack) input =
  (reduceAndGoto 47 states, StackElement_Decls ( AST.Sequence v1 v3 ) : stack, input)
reduce 48 states (StackElement_Decl v1 : stack) input =
  (reduceAndGoto 48 states, StackElement_Decls ( v1 ) : stack, input)
reduce 49 states (_ : stack) input =
  (reduceAndGoto 49 states, StackElement_Type ( TInt ) : stack, input)
reduce 50 states (_ : stack) input =
  (reduceAndGoto 50 states, StackElement_Type ( TDouble ) : stack, input)
reduce 51 states (_ : stack) input =
  (reduceAndGoto 51 states, StackElement_Type ( TChar ) : stack, input)
reduce 52 states (_ : stack) input =
  (reduceAndGoto 52 states, StackElement_Type ( TRef ) : stack, input)
reduce 53 states (_ : StackElement_Types v3 : _ : StackElement_Type v1 : stack) input =
  (reduceAndGoto 53 states, StackElement_Type ( TFunction v1 v3 ) : stack, input)
reduce 54 states (_ : _ : StackElement_Type v1 : stack) input =
  (reduceAndGoto 54 states, StackElement_Type ( TArray v1 ) : stack, input)
reduce 55 states (StackElement_Type v3 : _ : StackElement_Types v1 : stack) input =
  (reduceAndGoto 55 states, StackElement_Types ( TypeSequence v1 v3 ) : stack, input)
reduce 56 states (StackElement_Type v1 : stack) input =
  (reduceAndGoto 56 states, StackElement_Types ( v1 ) : stack, input)
reduce 57 states (StackElement_Bterm v3 : _ : StackElement_Bexpr v1 : stack) input =
  (reduceAndGoto 57 states, StackElement_Bexpr ( AST.LogOp Or v1 v3 ) : stack, input)
reduce 58 states (StackElement_Bterm v1 : stack) input =
  (reduceAndGoto 58 states, StackElement_Bexpr ( v1 ) : stack, input)
reduce 59 states (StackElement_Bfactor v3 : _ : StackElement_Bterm v1 : stack) input =
  (reduceAndGoto 59 states, StackElement_Bterm ( AST.LogOp And v1 v3 ) : stack, input)
reduce 60 states (StackElement_Bfactor v1 : stack) input =
  (reduceAndGoto 60 states, StackElement_Bterm ( v1 ) : stack, input)
reduce 61 states (_ : StackElement_Bexpr v2 : _ : stack) input =
  (reduceAndGoto 61 states, StackElement_Bfactor ( v2 ) : stack, input)
reduce 62 states (StackElement_Bfactor v2 : _ : stack) input =
  (reduceAndGoto 62 states, StackElement_Bfactor ( AST.Not v2 ) : stack, input)
reduce 63 states (StackElement_Expr v3 : StackTerminal ( PosToken _ (RelOp v2) ) : StackElement_Expr v1 : stack) input =
  (reduceAndGoto 63 states, StackElement_Bfactor ( AST.Comparison v2 v1 v3 ) : stack, input)
reduce 64 states (StackTerminal ( PosToken _ (DBool v1) ) : stack) input =
  (reduceAndGoto 64 states, StackElement_Bfactor ( AST.Boolean v1 ) : stack, input)
reduce 65 states (_ : stack) input =
  (reduceAndGoto 65 states, StackElement_Bfactor ( AST.Eof ) : stack, input)

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
    reduceList = [1,1,3,1,3,4,6,4,1,3,5,2,2,2,1,0,3,3,1,3,3,3,1,2,2,1,3,1,3,1,4,4,3,3,2,1,3,1,1,1,1,3,2,1,7,5,2,3,1,1,1,1,1,4,3,3,1,3,1,3,1,3,2,3,1,1]

-- | Returns the number of the non-terminal symbol for a given rule.
lhs
  :: RuleNumber
  -> NonTerminal
lhs = (lhsList !!)
  where
    lhsList :: [NonTerminal]
    lhsList = [0,1,2,2,3,3,3,3,3,4,4,4,4,4,4,4,5,5,5,6,6,6,6,7,7,7,8,8,9,9,10,10,10,10,10,10,11,11,12,12,12,12,12,12,13,13,13,14,14,15,15,15,15,15,15,16,16,17,17,18,18,19,19,19,19,19]

-- | For a given state and non-terminal symbol returns the next state we will
--   enter.
goto
  :: State
  -> NonTerminal
  -> State
goto 0 1 = 15
goto 0 2 = 16
goto 0 3 = 17
goto 0 4 = 18
goto 0 8 = 19
goto 0 10 = 20
goto 0 13 = 21
goto 0 15 = 22
goto 3 8 = 26
goto 3 10 = 20
goto 4 5 = 34
goto 4 6 = 35
goto 4 7 = 36
goto 4 8 = 37
goto 4 10 = 20
goto 4 12 = 38
goto 5 5 = 39
goto 5 6 = 35
goto 5 7 = 36
goto 5 8 = 37
goto 5 10 = 20
goto 5 12 = 38
goto 6 5 = 44
goto 6 6 = 35
goto 6 7 = 36
goto 6 8 = 37
goto 6 10 = 20
goto 6 12 = 38
goto 6 17 = 45
goto 6 18 = 46
goto 6 19 = 47
goto 7 5 = 44
goto 7 6 = 35
goto 7 7 = 36
goto 7 8 = 37
goto 7 10 = 20
goto 7 12 = 38
goto 7 17 = 48
goto 7 18 = 46
goto 7 19 = 47
goto 12 15 = 49
goto 14 2 = 51
goto 14 3 = 17
goto 14 4 = 18
goto 14 8 = 19
goto 14 10 = 20
goto 14 13 = 21
goto 14 15 = 22
goto 24 9 = 61
goto 24 10 = 62
goto 32 7 = 65
goto 32 8 = 37
goto 32 10 = 20
goto 32 12 = 38
goto 41 5 = 44
goto 41 6 = 35
goto 41 7 = 36
goto 41 8 = 37
goto 41 10 = 20
goto 41 12 = 38
goto 41 19 = 72
goto 43 5 = 44
goto 43 6 = 35
goto 43 7 = 36
goto 43 8 = 37
goto 43 10 = 20
goto 43 12 = 38
goto 43 17 = 73
goto 43 18 = 46
goto 43 19 = 47
goto 52 3 = 83
goto 52 4 = 18
goto 52 8 = 19
goto 52 10 = 20
goto 52 13 = 21
goto 52 15 = 22
goto 53 5 = 84
goto 53 6 = 35
goto 53 7 = 36
goto 53 8 = 37
goto 53 10 = 20
goto 53 12 = 38
goto 54 8 = 37
goto 54 10 = 20
goto 54 11 = 86
goto 54 12 = 87
goto 55 5 = 88
goto 55 6 = 35
goto 55 7 = 36
goto 55 8 = 37
goto 55 10 = 20
goto 55 12 = 38
goto 57 15 = 89
goto 57 16 = 90
goto 58 5 = 92
goto 58 6 = 35
goto 58 7 = 36
goto 58 8 = 37
goto 58 10 = 20
goto 58 12 = 38
goto 67 6 = 95
goto 67 7 = 36
goto 67 8 = 37
goto 67 10 = 20
goto 67 12 = 38
goto 68 6 = 96
goto 68 7 = 36
goto 68 8 = 37
goto 68 10 = 20
goto 68 12 = 38
goto 69 7 = 97
goto 69 8 = 37
goto 69 10 = 20
goto 69 12 = 38
goto 70 7 = 98
goto 70 8 = 37
goto 70 10 = 20
goto 70 12 = 38
goto 71 7 = 99
goto 71 8 = 37
goto 71 10 = 20
goto 71 12 = 38
goto 74 5 = 101
goto 74 6 = 35
goto 74 7 = 36
goto 74 8 = 37
goto 74 10 = 20
goto 74 12 = 38
goto 75 5 = 44
goto 75 6 = 35
goto 75 7 = 36
goto 75 8 = 37
goto 75 10 = 20
goto 75 12 = 38
goto 75 18 = 102
goto 75 19 = 47
goto 76 3 = 103
goto 76 4 = 18
goto 76 8 = 19
goto 76 10 = 20
goto 76 13 = 21
goto 76 15 = 22
goto 77 5 = 44
goto 77 6 = 35
goto 77 7 = 36
goto 77 8 = 37
goto 77 10 = 20
goto 77 12 = 38
goto 77 19 = 104
goto 78 3 = 105
goto 78 4 = 18
goto 78 8 = 19
goto 78 10 = 20
goto 78 13 = 21
goto 78 15 = 22
goto 81 13 = 107
goto 81 14 = 108
goto 81 15 = 109
goto 93 10 = 116
goto 106 13 = 107
goto 106 14 = 118
goto 106 15 = 109
goto 111 8 = 37
goto 111 10 = 20
goto 111 12 = 121
goto 114 15 = 122
goto 115 8 = 123
goto 115 10 = 20
goto 117 3 = 124
goto 117 4 = 18
goto 117 8 = 19
goto 117 10 = 20
goto 117 13 = 21
goto 117 15 = 22
goto 120 13 = 126
goto 120 15 = 109
goto 125 3 = 127
goto 125 4 = 18
goto 125 8 = 19
goto 125 10 = 20
goto 125 13 = 21
goto 125 15 = 22

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
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  Just ( PosToken _  Read ) -> shift 3 states stack input
  Just ( PosToken _  Output ) -> shift 4 states stack input
  Just ( PosToken _  Return ) -> shift 5 states stack input
  Just ( PosToken _  If ) -> shift 6 states stack input
  Just ( PosToken _  While ) -> shift 7 states stack input
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 14 states stack input
  Nothing -> reduce 15 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 15 states stack input
  Just ( PosToken _  Else ) -> reduce 15 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':', read, output, return, if, while, int, double, char, ref, func, labelspec, '{', 'eof', ')', ';', '}', else"
state states@(1:_) stack input = case headMay input of
  Just ( PosToken _ NameSpace) -> shift 23 states stack input
  Just ( PosToken _ Dot) -> shift 24 states stack input
  Nothing -> reduce 35 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 35 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 35 states stack input
  Just ( PosToken _ Dot) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 35 states stack input
  Just ( PosToken _  Assign ) -> reduce 35 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 35 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 35 states stack input
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
               ++ "\nexpecting ':', '.', 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then"
state states@(2:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 25 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(3:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':'"
state states@(4:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(5:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(6:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DBool _) ) -> shift 40 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _  Not ) -> shift 41 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  Just ( PosToken _  Eof ) -> shift 42 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 43 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, toClass, '-', ':', eof, '('"
state states@(7:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DBool _) ) -> shift 40 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _  Not ) -> shift 41 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  Just ( PosToken _  Eof ) -> shift 42 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 43 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, toClass, '-', ':', eof, '('"
state states@(8:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> reduce 49 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 49 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 49 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 49 states stack input
  Just ( PosToken _ (Id _) ) -> reduce 49 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', ')', ';', '[', id"
state states@(9:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> reduce 50 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 50 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 50 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 50 states stack input
  Just ( PosToken _ (Id _) ) -> reduce 50 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', ')', ';', '[', id"
state states@(10:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> reduce 51 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 51 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 51 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 51 states stack input
  Just ( PosToken _ (Id _) ) -> reduce 51 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', ')', ';', '[', id"
state states@(11:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> reduce 52 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 52 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 52 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 52 states stack input
  Just ( PosToken _ (Id _) ) -> reduce 52 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', ')', ';', '[', id"
state states@(12:_) stack input = case headMay input of
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting int, double, char, ref"
state states@(13:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 50 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(14:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  Just ( PosToken _  Read ) -> shift 3 states stack input
  Just ( PosToken _  Output ) -> shift 4 states stack input
  Just ( PosToken _  Return ) -> shift 5 states stack input
  Just ( PosToken _  If ) -> shift 6 states stack input
  Just ( PosToken _  While ) -> shift 7 states stack input
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 14 states stack input
  Nothing -> reduce 15 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 15 states stack input
  Just ( PosToken _  Else ) -> reduce 15 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':', read, output, return, if, while, int, double, char, ref, func, labelspec, '{', 'eof', ')', ';', '}', else"
state states@(15:_) stack input = case headMay input of
  Nothing -> accept states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof'"
state states@(16:_) stack input = case headMay input of
  Just ( PosToken _ (Token ';') ) -> shift 52 states stack input
  Nothing -> reduce 1 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ';', 'eof'"
state states@(17:_) stack input = case headMay input of
  Nothing -> reduce 3 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 3 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 3 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(18:_) stack input = case headMay input of
  Nothing -> reduce 8 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 8 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 8 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 8 states stack input
  Just ( PosToken _  Else ) -> reduce 8 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"
state states@(19:_) stack input = case headMay input of
  Just ( PosToken _  Assign ) -> shift 53 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ':='"
state states@(20:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> shift 54 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 55 states stack input
  Nothing -> reduce 27 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 27 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 27 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 27 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 27 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 27 states stack input
  Just ( PosToken _  Assign ) -> reduce 27 states stack input
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
               ++ "\nexpecting '(', '[', 'eof', ')', '*', '+', '-', '/', ':=', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(21:_) stack input = case headMay input of
  Nothing -> reduce 14 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 14 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 14 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 14 states stack input
  Just ( PosToken _  Else ) -> reduce 14 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"
state states@(22:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 56 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 57 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 58 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, '(', '['"
state states@(23:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 59 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(24:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 60 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':'"
state states@(25:_) stack input = case headMay input of
  Nothing -> reduce 34 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 34 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 34 states stack input
  Just ( PosToken _ Dot) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 34 states stack input
  Just ( PosToken _  Assign ) -> reduce 34 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 34 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 34 states stack input
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
               ++ "\nexpecting 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then"
state states@(26:_) stack input = case headMay input of
  Nothing -> reduce 12 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 12 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 12 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 12 states stack input
  Just ( PosToken _  Else ) -> reduce 12 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"
state states@(27:_) stack input = case headMay input of
  Just ( PosToken _ NameSpace) -> shift 63 states stack input
  Just ( PosToken _ Dot) -> shift 24 states stack input
  Nothing -> reduce 35 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 35 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 35 states stack input
  Just ( PosToken _ Dot) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 35 states stack input
  Just ( PosToken _  Assign ) -> reduce 35 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 35 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 35 states stack input
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
               ++ "\nexpecting ':', '.', 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then"
state states@(28:_) stack input = case headMay input of
  Nothing -> reduce 38 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 38 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 38 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 38 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 38 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 38 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 38 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 38 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 38 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 38 states stack input
  Just ( PosToken _  Do ) -> reduce 38 states stack input
  Just ( PosToken _  Else ) -> reduce 38 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 38 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 38 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 38 states stack input
  Just ( PosToken _  Then ) -> reduce 38 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(29:_) stack input = case headMay input of
  Nothing -> reduce 39 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 39 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 39 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 39 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 39 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 39 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 39 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 39 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 39 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 39 states stack input
  Just ( PosToken _  Do ) -> reduce 39 states stack input
  Just ( PosToken _  Else ) -> reduce 39 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 39 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 39 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 39 states stack input
  Just ( PosToken _  Then ) -> reduce 39 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(30:_) stack input = case headMay input of
  Nothing -> reduce 40 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 40 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 40 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 40 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 40 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 40 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 40 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 40 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 40 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 40 states stack input
  Just ( PosToken _  Do ) -> reduce 40 states stack input
  Just ( PosToken _  Else ) -> reduce 40 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 40 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 40 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 40 states stack input
  Just ( PosToken _  Then ) -> reduce 40 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(31:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 64 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(32:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(33:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 66 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(34:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 67 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 68 states stack input
  Nothing -> reduce 11 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 11 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 11 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 11 states stack input
  Just ( PosToken _  Else ) -> reduce 11 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', 'eof', ')', ';', '}', else"
state states@(35:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Times) ) -> shift 69 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> shift 70 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> shift 71 states stack input
  Nothing -> reduce 18 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 18 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 18 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 18 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 18 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 18 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 18 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 18 states stack input
  Just ( PosToken _  Do ) -> reduce 18 states stack input
  Just ( PosToken _  Else ) -> reduce 18 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 18 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 18 states stack input
  Just ( PosToken _  Then ) -> reduce 18 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '*', '/', mod, 'eof', ')', '+', '-', ';', ']', '}', and, do, else, or, relop, then"
state states@(36:_) stack input = case headMay input of
  Nothing -> reduce 22 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 22 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 22 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 22 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 22 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 22 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 22 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 22 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 22 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 22 states stack input
  Just ( PosToken _  Do ) -> reduce 22 states stack input
  Just ( PosToken _  Else ) -> reduce 22 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 22 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 22 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 22 states stack input
  Just ( PosToken _  Then ) -> reduce 22 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(37:_) stack input = case headMay input of
  Nothing -> reduce 43 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 43 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 43 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 43 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 43 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 43 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 43 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 43 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 43 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 43 states stack input
  Just ( PosToken _  Do ) -> reduce 43 states stack input
  Just ( PosToken _  Else ) -> reduce 43 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 43 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 43 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 43 states stack input
  Just ( PosToken _  Then ) -> reduce 43 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(38:_) stack input = case headMay input of
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
state states@(39:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 67 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 68 states stack input
  Nothing -> reduce 13 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 13 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 13 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 13 states stack input
  Just ( PosToken _  Else ) -> reduce 13 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', 'eof', ')', ';', '}', else"
state states@(40:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 64 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 64 states stack input
  Just ( PosToken _  Do ) -> reduce 64 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 64 states stack input
  Just ( PosToken _  Then ) -> reduce 64 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(41:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DBool _) ) -> shift 40 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _  Not ) -> shift 41 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  Just ( PosToken _  Eof ) -> shift 42 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 43 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, toClass, '-', ':', eof, '('"
state states@(42:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 65 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 65 states stack input
  Just ( PosToken _  Do ) -> reduce 65 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 65 states stack input
  Just ( PosToken _  Then ) -> reduce 65 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(43:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DBool _) ) -> shift 40 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _  Not ) -> shift 41 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  Just ( PosToken _  Eof ) -> shift 42 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 43 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, toClass, '-', ':', eof, '('"
state states@(44:_) stack input = case headMay input of
  Just ( PosToken _ (RelOp _) ) -> shift 74 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> shift 67 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 68 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting relop, '+', '-'"
state states@(45:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp Or) ) -> shift 75 states stack input
  Just ( PosToken _  Then ) -> shift 76 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting or, then"
state states@(46:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp And) ) -> shift 77 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 58 states stack input
  Just ( PosToken _  Do ) -> reduce 58 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 58 states stack input
  Just ( PosToken _  Then ) -> reduce 58 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting and, ')', do, or, then"
state states@(47:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 60 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 60 states stack input
  Just ( PosToken _  Do ) -> reduce 60 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 60 states stack input
  Just ( PosToken _  Then ) -> reduce 60 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(48:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp Or) ) -> shift 75 states stack input
  Just ( PosToken _  Do ) -> shift 78 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting or, do"
state states@(49:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 79 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 57 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 80 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, '(', '['"
state states@(50:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> shift 81 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '('"
state states@(51:_) stack input = case headMay input of
  Just ( PosToken _ (Token '}') ) -> shift 82 states stack input
  Just ( PosToken _ (Token ';') ) -> shift 52 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '}', ';'"
state states@(52:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  Just ( PosToken _  Read ) -> shift 3 states stack input
  Just ( PosToken _  Output ) -> shift 4 states stack input
  Just ( PosToken _  Return ) -> shift 5 states stack input
  Just ( PosToken _  If ) -> shift 6 states stack input
  Just ( PosToken _  While ) -> shift 7 states stack input
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 14 states stack input
  Nothing -> reduce 15 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 15 states stack input
  Just ( PosToken _  Else ) -> reduce 15 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':', read, output, return, if, while, int, double, char, ref, func, labelspec, '{', 'eof', ')', ';', '}', else"
state states@(53:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(54:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  Just ( PosToken _ (Token ')') ) -> shift 85 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, ':', ')'"
state states@(55:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(56:_) stack input = case headMay input of
  Nothing -> reduce 46 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 46 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 46 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 46 states stack input
  Just ( PosToken _  Else ) -> reduce 46 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"
state states@(57:_) stack input = case headMay input of
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting int, double, char, ref"
state states@(58:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  Just ( PosToken _ (Token ']') ) -> shift 91 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':', ']'"
state states@(59:_) stack input = case headMay input of
  Nothing -> reduce 33 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 33 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 33 states stack input
  Just ( PosToken _ Dot) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 33 states stack input
  Just ( PosToken _  Assign ) -> reduce 33 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 33 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 33 states stack input
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
               ++ "\nexpecting 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then"
state states@(60:_) stack input = case headMay input of
  Just ( PosToken _ NameSpace) -> shift 23 states stack input
  Nothing -> reduce 35 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 35 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 35 states stack input
  Just ( PosToken _ Dot) -> reduce 35 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 35 states stack input
  Just ( PosToken _  Assign ) -> reduce 35 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 35 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 35 states stack input
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
               ++ "\nexpecting ':', 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then"
state states@(61:_) stack input = case headMay input of
  Just ( PosToken _ Dot) -> shift 93 states stack input
  Nothing -> reduce 26 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 26 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 26 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 26 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 26 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 26 states stack input
  Just ( PosToken _  Assign ) -> reduce 26 states stack input
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
               ++ "\nexpecting '.', 'eof', ')', '*', '+', '-', '/', ':=', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(62:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> shift 54 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 55 states stack input
  Nothing -> reduce 29 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 29 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 29 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 29 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 29 states stack input
  Just ( PosToken _ Dot) -> reduce 29 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 29 states stack input
  Just ( PosToken _  Assign ) -> reduce 29 states stack input
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
               ++ "\nexpecting '(', '[', 'eof', ')', '*', '+', '-', '.', '/', ':=', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(63:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 94 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id"
state states@(64:_) stack input = case headMay input of
  Nothing -> reduce 23 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 23 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 23 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 23 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 23 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 23 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 23 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 23 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 23 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 23 states stack input
  Just ( PosToken _  Do ) -> reduce 23 states stack input
  Just ( PosToken _  Else ) -> reduce 23 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 23 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 23 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 23 states stack input
  Just ( PosToken _  Then ) -> reduce 23 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(65:_) stack input = case headMay input of
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
state states@(66:_) stack input = case headMay input of
  Nothing -> reduce 34 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 34 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 34 states stack input
  Just ( PosToken _ Dot) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 34 states stack input
  Just ( PosToken _  Assign ) -> reduce 34 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 34 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 34 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 34 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 34 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 34 states stack input
  Just ( PosToken _  Do ) -> reduce 34 states stack input
  Just ( PosToken _  Else ) -> reduce 34 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 34 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 34 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 34 states stack input
  Just ( PosToken _  Then ) -> reduce 34 states stack input
  Nothing -> reduce 42 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 42 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 42 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 42 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 42 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 42 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 42 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 42 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 42 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 42 states stack input
  Just ( PosToken _  Do ) -> reduce 42 states stack input
  Just ( PosToken _  Else ) -> reduce 42 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 42 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 42 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 42 states stack input
  Just ( PosToken _  Then ) -> reduce 42 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then, 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(67:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(68:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(69:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(70:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(71:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(72:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 62 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 62 states stack input
  Just ( PosToken _  Do ) -> reduce 62 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 62 states stack input
  Just ( PosToken _  Then ) -> reduce 62 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(73:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp Or) ) -> shift 75 states stack input
  Just ( PosToken _ (Token ')') ) -> shift 100 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting or, ')'"
state states@(74:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, toClass, '-', ':'"
state states@(75:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DBool _) ) -> shift 40 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _  Not ) -> shift 41 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  Just ( PosToken _  Eof ) -> shift 42 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 43 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, toClass, '-', ':', eof, '('"
state states@(76:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  Just ( PosToken _  Read ) -> shift 3 states stack input
  Just ( PosToken _  Output ) -> shift 4 states stack input
  Just ( PosToken _  Return ) -> shift 5 states stack input
  Just ( PosToken _  If ) -> shift 6 states stack input
  Just ( PosToken _  While ) -> shift 7 states stack input
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 14 states stack input
  Nothing -> reduce 15 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 15 states stack input
  Just ( PosToken _  Else ) -> reduce 15 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':', read, output, return, if, while, int, double, char, ref, func, labelspec, '{', 'eof', ')', ';', '}', else"
state states@(77:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DBool _) ) -> shift 40 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _  Not ) -> shift 41 states stack input
  Just ( PosToken _ ToClass) -> shift 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 32 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  Just ( PosToken _  Eof ) -> shift 42 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 43 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, bool, character, not, toClass, '-', ':', eof, '('"
state states@(78:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  Just ( PosToken _  Read ) -> shift 3 states stack input
  Just ( PosToken _  Output ) -> shift 4 states stack input
  Just ( PosToken _  Return ) -> shift 5 states stack input
  Just ( PosToken _  If ) -> shift 6 states stack input
  Just ( PosToken _  While ) -> shift 7 states stack input
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 14 states stack input
  Nothing -> reduce 15 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 15 states stack input
  Just ( PosToken _  Else ) -> reduce 15 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':', read, output, return, if, while, int, double, char, ref, func, labelspec, '{', 'eof', ')', ';', '}', else"
state states@(79:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> shift 106 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '('"
state states@(80:_) stack input = case headMay input of
  Just ( PosToken _ (Token ']') ) -> shift 91 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ']'"
state states@(81:_) stack input = case headMay input of
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting int, double, char, ref, func, labelspec"
state states@(82:_) stack input = case headMay input of
  Nothing -> reduce 4 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 4 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 4 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 4 states stack input
  Just ( PosToken _  Else ) -> reduce 4 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"
state states@(83:_) stack input = case headMay input of
  Nothing -> reduce 2 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 2 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 2 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ';', '}'"
state states@(84:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 67 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 68 states stack input
  Nothing -> reduce 9 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 9 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 9 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 9 states stack input
  Just ( PosToken _  Else ) -> reduce 9 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', 'eof', ')', ';', '}', else"
state states@(85:_) stack input = case headMay input of
  Nothing -> reduce 32 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 32 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 32 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 32 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 32 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 32 states stack input
  Just ( PosToken _ Dot) -> reduce 32 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 32 states stack input
  Just ( PosToken _  Assign ) -> reduce 32 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 32 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 32 states stack input
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
               ++ "\nexpecting 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then"
state states@(86:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> shift 110 states stack input
  Just ( PosToken _ (Token ';') ) -> shift 111 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(87:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 37 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 37 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(88:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 67 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 68 states stack input
  Just ( PosToken _ (Token ']') ) -> shift 112 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ']'"
state states@(89:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> shift 57 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 80 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 56 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 56 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', '[', ')', ';'"
state states@(90:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> shift 113 states stack input
  Just ( PosToken _ (Token ';') ) -> shift 114 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(91:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> reduce 54 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 54 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 54 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 54 states stack input
  Just ( PosToken _ (Id _) ) -> reduce 54 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', ')', ';', '[', id"
state states@(92:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 67 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 68 states stack input
  Just ( PosToken _ (Token ']') ) -> shift 115 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ']'"
state states@(93:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 60 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':'"
state states@(94:_) stack input = case headMay input of
  Nothing -> reduce 33 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 33 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 33 states stack input
  Just ( PosToken _ Dot) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 33 states stack input
  Just ( PosToken _  Assign ) -> reduce 33 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 33 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 33 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 33 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 33 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 33 states stack input
  Just ( PosToken _  Do ) -> reduce 33 states stack input
  Just ( PosToken _  Else ) -> reduce 33 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 33 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 33 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 33 states stack input
  Just ( PosToken _  Then ) -> reduce 33 states stack input
  Nothing -> reduce 41 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 41 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 41 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 41 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 41 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 41 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 41 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 41 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 41 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 41 states stack input
  Just ( PosToken _  Do ) -> reduce 41 states stack input
  Just ( PosToken _  Else ) -> reduce 41 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 41 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 41 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 41 states stack input
  Just ( PosToken _  Then ) -> reduce 41 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then, 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(95:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Times) ) -> shift 69 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> shift 70 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> shift 71 states stack input
  Nothing -> reduce 16 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 16 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 16 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 16 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 16 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 16 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 16 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 16 states stack input
  Just ( PosToken _  Do ) -> reduce 16 states stack input
  Just ( PosToken _  Else ) -> reduce 16 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 16 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 16 states stack input
  Just ( PosToken _  Then ) -> reduce 16 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '*', '/', mod, 'eof', ')', '+', '-', ';', ']', '}', and, do, else, or, relop, then"
state states@(96:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Times) ) -> shift 69 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> shift 70 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> shift 71 states stack input
  Nothing -> reduce 17 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 17 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 17 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 17 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 17 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 17 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 17 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 17 states stack input
  Just ( PosToken _  Do ) -> reduce 17 states stack input
  Just ( PosToken _  Else ) -> reduce 17 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 17 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 17 states stack input
  Just ( PosToken _  Then ) -> reduce 17 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '*', '/', mod, 'eof', ')', '+', '-', ';', ']', '}', and, do, else, or, relop, then"
state states@(97:_) stack input = case headMay input of
  Nothing -> reduce 19 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 19 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 19 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 19 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 19 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 19 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 19 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 19 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 19 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 19 states stack input
  Just ( PosToken _  Do ) -> reduce 19 states stack input
  Just ( PosToken _  Else ) -> reduce 19 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 19 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 19 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 19 states stack input
  Just ( PosToken _  Then ) -> reduce 19 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(98:_) stack input = case headMay input of
  Nothing -> reduce 20 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 20 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 20 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 20 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 20 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 20 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 20 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 20 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 20 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 20 states stack input
  Just ( PosToken _  Do ) -> reduce 20 states stack input
  Just ( PosToken _  Else ) -> reduce 20 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 20 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 20 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 20 states stack input
  Just ( PosToken _  Then ) -> reduce 20 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(99:_) stack input = case headMay input of
  Nothing -> reduce 21 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 21 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 21 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 21 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 21 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 21 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 21 states stack input
  Just ( PosToken _ (Token ']') ) -> reduce 21 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 21 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 21 states stack input
  Just ( PosToken _  Do ) -> reduce 21 states stack input
  Just ( PosToken _  Else ) -> reduce 21 states stack input
  Just ( PosToken _ (MathOp Mod) ) -> reduce 21 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 21 states stack input
  Just ( PosToken _ (RelOp _) ) -> reduce 21 states stack input
  Just ( PosToken _  Then ) -> reduce 21 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', '*', '+', '-', '/', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(100:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 61 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 61 states stack input
  Just ( PosToken _  Do ) -> reduce 61 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 61 states stack input
  Just ( PosToken _  Then ) -> reduce 61 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(101:_) stack input = case headMay input of
  Just ( PosToken _ (MathOp Plus) ) -> shift 67 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> shift 68 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 63 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 63 states stack input
  Just ( PosToken _  Do ) -> reduce 63 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 63 states stack input
  Just ( PosToken _  Then ) -> reduce 63 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '+', '-', ')', and, do, or, then"
state states@(102:_) stack input = case headMay input of
  Just ( PosToken _ (LogOp And) ) -> shift 77 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 57 states stack input
  Just ( PosToken _  Do ) -> reduce 57 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 57 states stack input
  Just ( PosToken _  Then ) -> reduce 57 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting and, ')', do, or, then"
state states@(103:_) stack input = case headMay input of
  Just ( PosToken _  Else ) -> shift 117 states stack input
  Nothing -> reduce 5 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 5 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 5 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 5 states stack input
  Just ( PosToken _  Else ) -> reduce 5 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting else, 'eof', ')', ';', '}', else"
state states@(104:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 59 states stack input
  Just ( PosToken _ (LogOp And) ) -> reduce 59 states stack input
  Just ( PosToken _  Do ) -> reduce 59 states stack input
  Just ( PosToken _ (LogOp Or) ) -> reduce 59 states stack input
  Just ( PosToken _  Then ) -> reduce 59 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', and, do, or, then"
state states@(105:_) stack input = case headMay input of
  Nothing -> reduce 7 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 7 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 7 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 7 states stack input
  Just ( PosToken _  Else ) -> reduce 7 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"
state states@(106:_) stack input = case headMay input of
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting int, double, char, ref, func, labelspec"
state states@(107:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 48 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 48 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(108:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> shift 119 states stack input
  Just ( PosToken _ (Token ';') ) -> shift 120 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(109:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 56 states stack input
  Just ( PosToken _ (Token '(') ) -> shift 57 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 80 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, '(', '['"
state states@(110:_) stack input = case headMay input of
  Nothing -> reduce 31 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 31 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 31 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 31 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 31 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 31 states stack input
  Just ( PosToken _ Dot) -> reduce 31 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 31 states stack input
  Just ( PosToken _  Assign ) -> reduce 31 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 31 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 31 states stack input
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
               ++ "\nexpecting 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then"
state states@(111:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 27 states stack input
  Just ( PosToken _ (DInt _) ) -> shift 28 states stack input
  Just ( PosToken _ (DDouble _) ) -> shift 29 states stack input
  Just ( PosToken _ (DChar _) ) -> shift 30 states stack input
  Just ( PosToken _ NameSpace) -> shift 33 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, integer, real, character, ':'"
state states@(112:_) stack input = case headMay input of
  Nothing -> reduce 30 states stack input
  Just ( PosToken _ (Token '(') ) -> reduce 30 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 30 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 30 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 30 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 30 states stack input
  Just ( PosToken _ Dot) -> reduce 30 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 30 states stack input
  Just ( PosToken _  Assign ) -> reduce 30 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 30 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 30 states stack input
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
               ++ "\nexpecting 'eof', '(', ')', '*', '+', '-', '.', '/', ':=', ';', '[', ']', '}', and, do, else, mod, or, relop, then"
state states@(113:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> reduce 53 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 53 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 53 states stack input
  Just ( PosToken _ (Token '[') ) -> reduce 53 states stack input
  Just ( PosToken _ (Id _) ) -> reduce 53 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', ')', ';', '[', id"
state states@(114:_) stack input = case headMay input of
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting int, double, char, ref"
state states@(115:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':'"
state states@(116:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> shift 54 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 55 states stack input
  Nothing -> reduce 28 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 28 states stack input
  Just ( PosToken _ (MathOp Times) ) -> reduce 28 states stack input
  Just ( PosToken _ (MathOp Plus) ) -> reduce 28 states stack input
  Just ( PosToken _ (MathOp Minus) ) -> reduce 28 states stack input
  Just ( PosToken _ Dot) -> reduce 28 states stack input
  Just ( PosToken _ (MathOp DivBy) ) -> reduce 28 states stack input
  Just ( PosToken _  Assign ) -> reduce 28 states stack input
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
               ++ "\nexpecting '(', '[', 'eof', ')', '*', '+', '-', '.', '/', ':=', ';', ']', '}', and, do, else, mod, or, relop, then"
state states@(117:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  Just ( PosToken _  Read ) -> shift 3 states stack input
  Just ( PosToken _  Output ) -> shift 4 states stack input
  Just ( PosToken _  Return ) -> shift 5 states stack input
  Just ( PosToken _  If ) -> shift 6 states stack input
  Just ( PosToken _  While ) -> shift 7 states stack input
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 14 states stack input
  Nothing -> reduce 15 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 15 states stack input
  Just ( PosToken _  Else ) -> reduce 15 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':', read, output, return, if, while, int, double, char, ref, func, labelspec, '{', 'eof', ')', ';', '}', else"
state states@(118:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> shift 125 states stack input
  Just ( PosToken _ (Token ';') ) -> shift 120 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(119:_) stack input = case headMay input of
  Nothing -> reduce 45 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 45 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 45 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 45 states stack input
  Just ( PosToken _  Else ) -> reduce 45 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"
state states@(120:_) stack input = case headMay input of
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting int, double, char, ref, func, labelspec"
state states@(121:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 36 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 36 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(122:_) stack input = case headMay input of
  Just ( PosToken _ (Token '(') ) -> shift 57 states stack input
  Just ( PosToken _ (Token '[') ) -> shift 80 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 55 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 55 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting '(', '[', ')', ';'"
state states@(123:_) stack input = case headMay input of
  Nothing -> reduce 10 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 10 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 10 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 10 states stack input
  Just ( PosToken _  Else ) -> reduce 10 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"
state states@(124:_) stack input = case headMay input of
  Nothing -> reduce 6 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 6 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 6 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 6 states stack input
  Just ( PosToken _  Else ) -> reduce 6 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"
state states@(125:_) stack input = case headMay input of
  Just ( PosToken _ (Id _) ) -> shift 1 states stack input
  Just ( PosToken _ NameSpace) -> shift 2 states stack input
  Just ( PosToken _  Read ) -> shift 3 states stack input
  Just ( PosToken _  Output ) -> shift 4 states stack input
  Just ( PosToken _  Return ) -> shift 5 states stack input
  Just ( PosToken _  If ) -> shift 6 states stack input
  Just ( PosToken _  While ) -> shift 7 states stack input
  Just ( PosToken _ (Type TInt) ) -> shift 8 states stack input
  Just ( PosToken _ (Type TDouble) ) -> shift 9 states stack input
  Just ( PosToken _ (Type TChar) ) -> shift 10 states stack input
  Just ( PosToken _ (Type TRef)) -> shift 11 states stack input
  Just ( PosToken _  Function ) -> shift 12 states stack input
  Just ( PosToken _ LabelSpec) -> shift 13 states stack input
  Just ( PosToken _ (Token '{') ) -> shift 14 states stack input
  Nothing -> reduce 15 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 15 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 15 states stack input
  Just ( PosToken _  Else ) -> reduce 15 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting id, ':', read, output, return, if, while, int, double, char, ref, func, labelspec, '{', 'eof', ')', ';', '}', else"
state states@(126:_) stack input = case headMay input of
  Just ( PosToken _ (Token ')') ) -> reduce 47 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 47 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting ')', ';'"
state states@(127:_) stack input = case headMay input of
  Nothing -> reduce 44 states stack input
  Just ( PosToken _ (Token ')') ) -> reduce 44 states stack input
  Just ( PosToken _ (Token ';') ) -> reduce 44 states stack input
  Just ( PosToken _ (Token '}') ) -> reduce 44 states stack input
  Just ( PosToken _  Else ) -> reduce 44 states stack input
  _ -> error $ "unexpected " ++
               if null input then "end of file" else show (head input)
               ++ "\nexpecting 'eof', ')', ';', '}', else"

state states stack input = error $
  "Reached a non-defined state.\nStates: " ++ show states ++ "\nStack: " ++
  show stack ++ "\nInput: " ++ show input
