
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
type Input = [-- TEMPLATE:INPUT_TYPE
]
-- | The user-defined output type (the type of the first rule).
type Output = -- TEMPLATE:OUTPUT_TYPE

-- | The first constructor is for all tokens and the following constructors are
--   for the respective non-terminal symbols.
data StackElement
  -- TEMPLATE:STACK_ELEMENTS
  deriving (Show)

-- | The main parsing function. Repeatedly applies a transformation until an
--   'accept' definition is reached.
-- TEMPLATE:FUNCTION_NAME
 :: Input -> Output
-- TEMPLATE:FUNCTION_NAME
 inp = parse' ([0], [], inp)
  where
    parse' ([], [StackElement_-- TEMPLATE:RESULT_TYPE
 result], []) = result
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
-- TEMPLATE:REDUCE
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
    reduceList = -- TEMPLATE:REDUCE_LIST

-- | Returns the number of the non-terminal symbol for a given rule.
lhs
  :: RuleNumber
  -> NonTerminal
lhs = (lhsList !!)
  where
    lhsList :: [NonTerminal]
    lhsList = -- TEMPLATE:LHS_LIST

-- | For a given state and non-terminal symbol returns the next state we will
--   enter.
goto
  :: State
  -> NonTerminal
  -> State
-- TEMPLATE:GOTO
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
-- TEMPLATE:STATE
state states stack input = error $
  "Reached a non-defined state.\nStates: " ++ show states ++ "\nStack: " ++
  show stack ++ "\nInput: " ++ show input
