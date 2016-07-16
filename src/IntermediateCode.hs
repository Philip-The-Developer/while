{-# OPTIONS_HADDOCK ignore-exports #-}
{-# LANGUAGE MultiWayIf #-}
{-|
  Module      : IntermediateCode
  Description : Builds an intermediate code representation from an abstract
                syntax tree.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
                2016, Philip Schmiel
  License     : GPL-3
-}
module IntermediateCode (
  IntermediateCode.process
) where
import Prelude (
    Int,
    show,
    (+), ($), (++), (==),
    (||), (/=), (!!), (&&), (>),(-), not,
    String, Bool (..), Maybe (..), Int(..), error, putStrLn,
    fst, head, last, length, takeWhile, drop, concat, fromIntegral
  )
import Control.Monad.State (
    State,
    runState, get, put, return
  )
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (
    fromJust, isNothing, isJust
  )
import Data.String.Utils (
    split, endswith, replace
  )

import Data.Int (
    Int64
  )

import qualified Interface.Token as T
import qualified Interface.AST as AST
import qualified Interface.TAC as TAC
import GarbageCollection.GarbageCollection (
    dealloc
  )
-- $| The generator state has to track two counters, one for the temporary
-- variables and one for the labels, the mapping from variable to data type,
-- return type. Function signatures, function labels and variable location names,
-- for each is a map required too.
type GenState = (Counter, Environment, ReturnType,DataLabelScopes)
-- This counts temp variables and labels
type Counter = (TempCounter, LabelCounter)
-- | This is just a number.
type TempCounter = Int
-- | This is just a number.
type LabelCounter = Int
-- $| This is a mapping from variable to data type.
type Environment = [Map String (String, T.Type)]
-- $| This is just a string.
type Type = String
-- $| This is just a string.
type ReturnType = T.Type
-- TODO docu| This is a Map of frontend label names to a tupel of
type DataLabelScopes = Map String [AST.Command]
-- $| This is a list of UDF names and TACs.
type TACstream = [(TAC.Label, TAC.TAC)]

--TODO docu
getType:: AST.Command -> String
getType (AST.Declaration t n) = show t

-- $| Given an abstract syntax tree it generates and intermediate representation
-- in three address code and an appendix with user-defined functions for later use.
process :: AST.AST -> TACstream -- $ modified
process ast = ("",directives):("",intermediateCode):appendix
  where
    ((directives,intermediateCode,appendix), _) = runState (program ast) ((0,0),[Map.empty], T.Void, Map.insert "env:new" [AST.Declaration (T.TFunction T.TRef T.TRef) "new"] Map.empty)

-- | Generates a new label and increments the internal label counter.
newLabel :: State GenState (TAC.Label)
newLabel = do
  ((t,l),env,r,labels) <- get         -- $ modified
  put ((t,l+1),env,r,labels)          -- $ modified
  return $ "label" ++ show (l+1)

-- | Generates a new temporary variable and increments the internal variable
-- counter.
newTemp :: State GenState (TAC.Variable)
newTemp = do
  ((t,l),env,r,labels) <- get         -- $ modified
  put ((t+1,l),env,r,labels)          -- $ modified
  return $ "#" ++ show (t+1)

-- | Returns the variable given as parameter. To be used in 'expressionInto'.
fixedVar :: TAC.Variable -> State GenState TAC.Variable
fixedVar = return

-- $| Looks up type of variable.
lookup :: String -> State GenState (Maybe (String, T.Type))
lookup i = do
  (_,s,_,_) <- get
  let type_ = scopes i s
  return type_
  where
    scopes :: String -> Environment -> Maybe (String, T.Type)
    scopes _ [] = Nothing
    scopes i (m:_)
          | isJust _type = _type
        where 
          _type = Map.lookup i m
    scopes i (_:mm) = scopes i mm

lookupLabel :: String -> State GenState (Maybe [AST.Command])
lookupLabel str = do
  (_,_,_,labelMap) <- get
  return $ Map.lookup str labelMap

-- $| Changes the unique ID of a variable which correspond to a machine location.
insert :: String -> (String, T.Type) -> State GenState ()
insert i v =do
    (c,(h:t),r,labels) <- get
    let h' = Map.insert i v h
    put (c, (h':t),r,labels)
    return ()

-- $| Assigns a unique ID to a variable which correspond to a machine location.
{-newAlt :: String -> Locations -> (String, Locations)
newAlt i m = (name, a')
  where
    names = Map.lookup i m
    (name, a') = if isNothing names then (i ++ "_", Map.insert i [name] m) else (i ++ "_" ++ (show $ length $ fromJust names), Map.insert i ((fromJust names) ++ [name]) m) -}

-- $| Generates three address code for a complete program and an appendix with user-defined functions for later use.
program :: AST.AST -> State GenState (TAC.TAC, TAC.TAC, TACstream) -- $ modified
program prog = do
  next <- newLabel
  (directives,tac, udf, rt1) <- command prog next
  (_,_,r,_) <- get
  if r == T.Void || rt1 == r
    then return (directives, tac ++ [TAC.Label next], udf)
  else error $ "UDF has no return value."

-- $| Generates three address code for one specific command in the AST,
-- an appendix with user-defined functions for later use and
-- checks the existence of a return statement.
command :: AST.Command -> TAC.Label -> State GenState (TAC.TAC, TAC.TAC, TACstream, ReturnType) -- $ modified
command cmd next = case cmd of
  (AST.Sequence c1 c2) -> do
    (dir1, tac1, stream1, type1) <- command c1 next
    (dir2, tac2, stream2, type2) <- command c2 next
    return (dir1++dir2, tac1++tac2, stream1++stream2, if type1 == T.Void then type2 else type1)
 
  (AST.Declaration typ id) -> do
    declaredType <- lookup id
    if not $ isNothing declaredType
      then error $ "Variable \""++id++"\" has been declared twice."
      else do
        insert id (id,typ)
        return ([],[],[],T.Void)

  (AST.Assign adr expr) -> do
    (dir1, tac1, var1, type1) <- address adr
    (dir2, tac2, dat2, type2) <- expression expr
    return (dir1++dir2,tac1++tac2++[TAC.Copy (var1) dat2],[], type1)
 
  (AST.While bex cmd) -> do
    labelLoop <- newLabel
    labelTrue <- newLabel
    labelFalse <- newLabel
    (dir1, tac1) <- boolExpression bex labelTrue labelFalse
    (dir2, tac2, stream, type_) <- command cmd labelFalse
    return (dir1++dir2, [TAC.Label labelLoop]++ tac1++[TAC.Label labelTrue]++tac2++[TAC.Goto labelLoop]++[TAC.Label labelFalse], stream, type_)

  (AST.Environment cmd) -> do
    (c,env,r,lm) <- get
    put (c, Map.empty:env,r,lm)
    (dir,tac,stream,type_) <- command cmd next
    (c', (h:t), r', lm') <- get
    put (c', t , r', lm')
    return (dir, tac, stream, type_)

  (AST.IfThen bexpr cmd) -> do
    labelTrue <- newLabel
    labelFalse <- newLabel
    (dir1, tac1) <- boolExpression bexpr labelTrue labelFalse
    (dir2, tac2, stream, type_) <- command cmd next
    return (dir1++dir2, tac1++[TAC.Label labelTrue]++tac2++[TAC.Label labelFalse], stream, type_)

  (AST.IfThenElse bexpr cmd1 cmd2) -> do
    labelTrue <- newLabel
    labelFalse <- newLabel
    labelEnd <- newLabel
    (dir1, tac1) <- boolExpression bexpr labelTrue labelFalse
    (dir2, tac2, stream2, type2) <- command cmd1 next
    (dir3, tac3, stream3, type3) <- command cmd2 next
    return (dir1++dir2++dir3, tac1++[TAC.Label labelTrue]++tac2++[TAC.Goto labelEnd, TAC.Label labelFalse]++tac3++[TAC.Label labelEnd], stream2++stream3, if type2 == T.Void then type3 else type2)
    

  (AST.Output expr) ->do
    (dir1, tac1, var1, type1) <- expression expr
    case type1 of
      (T.TInt) -> return (dir1,tac1++[TAC.Output var1], [], T.Void)
      (T.TChar) -> return (dir1, tac1++ [TAC.COutput var1], [], T.Void)
      (T.TDouble) -> return (dir1, tac1++ [TAC.FOutput var1], [], T.Void)
      otherwise -> error $ "output is only suported for int, char and double outputs.\n The expression \""++show expr++"\" has returns type \""++show type1++"\"."

  (AST.Read addr) -> do
    (dir1, tac1, var1, type1) <- address addr
    case type1 of
      (T.TInt) -> return (dir1,tac1++[TAC.Read var1], [], T.Void)
      (T.TChar) -> return (dir1, tac1++ [TAC.CRead var1], [], T.Void)
      (T.TDouble) -> return (dir1, tac1++ [TAC.FRead var1], [], T.Void)
      otherwise -> error $ "read is only suported for int, char and double outputs.\n The expression \""++show addr++"\" has returns type \""++show type1++"\"."
      
  
  _ -> error $ "Command \""++show cmd++"\" can not be compiled into immediate code."  
-- $| Generates three address code for one expression in the AST (possibly
-- generating code for subexpressions first) and determines its type.
expression :: AST.Expression -> State GenState (TAC.TAC,TAC.TAC,TAC.Data,T.Type)
expression = expressionInto newTemp

-- | Generates three address code for one expression in the AST (possibly
-- generating code for subexpressions first). The additional parameter will be
-- evaluated if code for something other than number or identifier is generated
-- and the returned variable will be used for the result.
-- $ Determines also its type.
expressionInto :: State GenState TAC.Variable -> AST.Expression
               -> State GenState (TAC.TAC,TAC.TAC,TAC.Data,T.Type) -- $ modified
expressionInto varFunc expr = case expr of
  (AST.Integer i) -> return ([],[],TAC.ImmediateInteger i,T.TInt)
  (AST.Double d) -> return ([],[],TAC.ImmediateDouble d, T.TDouble)
  (AST.Reference s r) -> return ([],[],TAC.ImmediateReference s r, T.TRef)
  (AST.Character c) -> return ([],[],TAC.ImmediateChar c, T.TChar)

  (AST.Variable addr) -> do
    (dir, tac, var, type_) <- address addr
    return (dir,tac, TAC.Variable var,type_)

  (AST.Calculation op expr1 expr2) -> do
    (dir1, tac1, dat1, type1) <- expression expr1
    (dir2, tac2, dat2, type2) <- expression expr2
    (conv, dat1', dat2', type') <-  convert dat1 type1 dat2 type2
    var' <- newTemp
    let var = var' ++":"++show type'
    return (dir1++dir2, tac1++tac2++conv++[TAC.getCalculation op type' var dat1' dat2'], TAC.Variable var, type')

  _ -> error $ "Expression \""++show expr++"\" can not be compiled into immediate code."

address :: AST.Address -> State GenState (TAC.TAC, TAC.TAC, String, T.Type)
address (AST.Identifier i) =do
  vt <- lookup i
  if isNothing vt
  then error $ "Variable \""++i++"\" has not been declaret."
  else do
    let (var, type_) = fromJust vt
    return ([],[], var++":"++show type_, type_)
address adr = error $ "Address \""++show adr++"\" can not be compiled into immediate code." 

-- | Generates three address code for one boolean expression in the AST
-- (possibly generating code for boolean subexpressions first).
boolExpression :: AST.BoolExpression -> TAC.Label -> TAC.Label
               -> State GenState (TAC.TAC, TAC.TAC)
boolExpression bexpr lTrue lFalse = case bexpr of
  AST.LogOp op b1 b2 -> case op of
    T.And -> do
      b1True <- newLabel
      (dir1,tac1) <- boolExpression b1 b1True lFalse
      (dir2,tac2) <- boolExpression b2 lTrue lFalse
      return $ (dir1++dir2,tac1 ++ [TAC.Label b1True] ++ tac2)
    T.Or -> do
      b1False <- newLabel
      (dir1,tac1) <- boolExpression b1 lTrue b1False
      (dir2, tac2) <- boolExpression b2 lTrue lFalse
      return $ (dir1++dir2, tac1 ++ [TAC.Label b1False] ++ tac2)
  AST.Comparison op e1 e2 -> do
    (dir1, tac1,data1,type1) <- expression e1  -- $ modified
    (dir2, tac2,data2,type2) <- expression e2  -- $ modified
    if T.isArray type1 || T.isArray type2 -- $ added
      then error "Cannot use an array in a comparison."
    else do
      let jump1 = case op of
                T.Eq -> \l -> TAC.GotoCond2 l TAC.FEqual data1 data2
                T.Neq -> \l -> TAC.GotoCond2 l TAC.FNotEqual data1 data2
                T.Lt -> \l -> TAC.GotoCond2 l TAC.FLess data1 data2
                T.Lte -> \l -> TAC.GotoCond2 l TAC.FLessEqual data1 data2
                T.Gt -> \l -> TAC.GotoCond2 l TAC.FGreater data1 data2
                T.Gte -> \l -> TAC.GotoCond2 l TAC.FGreaterEqual data1 data2
      let jump2 = case op of
            T.Eq -> \l -> TAC.GotoCond2 l TAC.Equal data1 data2
            T.Neq -> \l -> TAC.GotoCond2 l TAC.NotEqual data1 data2
            T.Lt -> \l -> TAC.GotoCond2 l TAC.Less data1 data2
            T.Lte -> \l -> TAC.GotoCond2 l TAC.LessEqual data1 data2
            T.Gt -> \l -> TAC.GotoCond2 l TAC.Greater data1 data2
            T.Gte -> \l -> TAC.GotoCond2 l TAC.GreaterEqual data1 data2
      let jump = if type1 == T.TDouble || type2 == T.TDouble then jump1 else jump2
      return $ (dir1++dir2, tac1 ++ tac2 ++ [jump lTrue] ++ [TAC.Goto lFalse])
  AST.Not b -> boolExpression b lFalse lTrue
  AST.Boolean b -> return ([],[TAC.Goto (if b then lTrue else lFalse)])
  AST.Eof -> return ([],[ TAC.GotoCond1 lTrue TAC.IsTrue (TAC.Variable "%eof%")
                    , TAC.Goto lFalse
                    ])
convert:: TAC.Data -> T.Type -> TAC.Data -> T.Type -> State GenState (TAC.TAC, TAC.Data, TAC.Data, T.Type)
convert data1 type1 data2 type2 = do
      if (type1 == type2) then return ([], data1, data2, type1)
      else if (type1 == T.TDouble && type2 == T.TInt) then do
        var' <- newTemp
        let var = var'++":double"
        case data2 of
          (TAC.Variable _) -> return ([TAC.Convert var data2], data1, TAC.Variable var, T.TDouble)
          _ -> return ([], data1,data2,T.TDouble)
      else if (type1 == T.TInt && type2 == T.TDouble) then do
        var' <- newTemp
        let var = var'++":double"
        case data1 of
          (TAC.Variable _) -> return ([TAC.Convert var data1], TAC.Variable var, data2, T.TDouble)
          _ -> return ([],data1, data2,T.TDouble)
      else error $ "Can not convert \""++show type1++"\" to \""++show type1++"\" or \""++show type2++"\" to \""++show type1++"\"."

mapType :: T.Type -> State GenState (TAC.TAC, String)
mapType t = case t of
  _ -> return ([], T.getLabel t)
