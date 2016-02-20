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
    (||), (/=), (!!), (&&), (>), not,
    String, Bool (..), Maybe (..), error,
    fst, head, last, length, takeWhile
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
    split, endswith
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
type GenState = (TempCounter, LabelCounter, Environment, ReturnType, FunctionScopes, UDFLabels, Locations)
-- | This is just a number.
type TempCounter = Int
-- | This is just a number.
type LabelCounter = Int
-- $| This is a mapping from variable to data type.
type Environment = [Map String String]
-- $| This is just a string.
type Type = String
-- $| This is just a string.
type ReturnType = String
-- $| This is a list of maps representing scopes of user-defined functions.
type FunctionScopes = [Map String String]
-- $| This is a map of reserved labels for user-defined functions.
type UDFLabels = Map String [String]
-- $| This is a list of UDF names and TACs.
type TACstream = [(TAC.Label, TAC.TAC)]
-- $| This is a map of reserved locations.
type Locations = Map String [String]

-- $| Given an abstract syntax tree it generates and intermediate representation
-- in three address code and an appendix with user-defined functions for later use.
process :: AST.AST -> TACstream -- $ modified
process ast = ("",intermediateCode):appendix
  where
    ((intermediateCode,appendix), _) = runState (program ast) (0,0,[Map.empty], "void", [Map.singleton "length" "length_:int:any[]"], Map.empty, Map.singleton "length" ["length_"])

-- | Generates a new label and increments the internal label counter.
newLabel :: State GenState TAC.Label
newLabel = do
  (t,l,s,r,f,u,a) <- get         -- $ modified
  put (t,l+1,s,r,f,u,a)          -- $ modified
  return $ "label" ++ show (l+1)

-- | Generates a new temporary variable and increments the internal variable
-- counter.
newTemp :: State GenState TAC.Variable
newTemp = do
  (t,l,s,r,f,u,a) <- get     -- $ modified
  put (t+1,l,s,r,f,u,a)      -- $ modified
  return $ "#" ++ show (t+1)

-- | Returns the variable given as parameter. To be used in 'expressionInto'.
fixedVar :: TAC.Variable -> State GenState TAC.Variable
fixedVar = return

-- $| Looks up type of variable.
lookup :: String -> Bool -> State GenState (Maybe String)
lookup i u = do
  (_,_,s,_,f,_,_) <- get
  let type_ = if u then scopes i f else scopes i s
  return type_
  where
    scopes :: String -> Environment -> Maybe String
    scopes _ [] = Nothing
    scopes i (m:_)
          | isJust _type = _type
        where 
          _type = Map.lookup i m
    scopes i (_:mm) = scopes i mm

-- $| Changes the unique ID of a variable which correspond to a machine location.
insert :: String -> String -> Environment -> Environment
insert i v (m:mm)
  | isJust type_ = (Map.insert i v m):mm
  where type_ = Map.lookup i m
insert i v (m:mm) = m:(insert i v mm)

-- $| Assigns a unique ID to a variable which correspond to a machine location.
newAlt :: String -> Locations -> (String, Locations)
newAlt i m = (name, a')
  where
    names = Map.lookup i m
    (name, a') = if isNothing names then (i ++ "_", Map.insert i [name] m) else (i ++ "_" ++ (show $ length $ fromJust names), Map.insert i ((fromJust names) ++ [name]) m)

-- $| Generates three address code for a complete program and an appendix with user-defined functions for later use.
program :: AST.AST -> State GenState (TAC.TAC, TACstream) -- $ modified
program prog = do
  next <- newLabel
  (tac, udf, rt1) <- command prog next
  (_,_,_,r,_,_,_) <- get
  let (function, rt2) = let list = split ":" r in (head list, last list)
  if r == "void" || rt1 == rt2
    then return (tac ++ [TAC.Label next], udf)
  else error $ "UDF " ++ function ++ " has no return value."

-- $| Generates three address code for one specific command in the AST,
-- an appendix with user-defined functions for later use and
-- checks the existence of a return statement.
command :: AST.Command -> TAC.Label -> State GenState (TAC.TAC, TACstream, ReturnType) -- $ modified
command cmd next = case cmd of
  AST.Output e -> do -- $ modified
    (tac,data_,type_) <- expression e
    if type_ == "int"
          then return (tac ++ [TAC.Output data_], [], "")
        else if type_ == "double"
          then return (tac ++ [TAC.FOutput data_], [], "")
        else if type_ == "char"
          then return (tac ++ [TAC.Output data_], [], "")
        else error "No native support for outputting arrays."
  AST.Return e -> do -- $ added
    (tac,data_,type_) <- expression e
    (_,_,_,r,_,_,_) <- get
    let (function, rt) = let list = split ":" r in (head list, last list)
    if r == "void"
          then return ([], [], "")
    else if type_ /= rt
          then error $ "A return instruction in UDF " ++ function ++ " delivers a value of wrong type."
    else if type_ == "double"
          then return (tac ++ [TAC.FReturn data_], [], type_)
        else return (tac ++ [TAC.Return data_], [], type_)
  AST.Read i -> do -- $ modified
    type_ <- lookup i False
    if endswith "]" $ fromJust type_
      then error $ "No native support for inputting arrays, i.e. to array " ++ i ++ "."
    else if endswith "int" $ fromJust type_
          then return ([TAC.Read $ fromJust type_], [], "")
        else if endswith "double" $ fromJust type_
          then return ([TAC.FRead $ fromJust type_], [], "")
        else error $ "Variable " ++ i ++ " has not been declared."
  AST.Skip -> return ([], [], "")
  AST.Sequence c1 c2 -> do -- $ modified
    next1 <- newLabel
    (tac1,udf1,rt1)  <- command c1 next1
    (tac2,udf2,rt2)  <- command c2 next
    return (tac1 ++ [TAC.Label next1] ++ tac2, udf1 ++ udf2, if rt1 /= "" then rt1 else rt2)
  AST.IfThen b c -> do
    true <- newLabel
    btac <- boolExpression b true next
    (tac,udf,rt) <- command c next -- $ modified
    return (btac ++ [TAC.Label true] ++ tac, udf, rt) -- $ modified
  AST.IfThenElse b c1 c2 ->do
    true <- newLabel
    false <- newLabel
    btac <- boolExpression b true false
    (tac1,udf1,rt1) <- command c1 next -- $ modified
    (tac2,udf2,rt2) <- command c2 next -- $ modified
    return (btac ++ [TAC.Label true] ++ tac1 ++ [TAC.Goto next, TAC.Label false] ++ tac2, udf1 ++ udf2, if rt1 /= "" then rt1 else rt2) -- $ modified
  AST.While b c -> do
    true <- newLabel
    btac <- boolExpression b true next
    begin <- newLabel
    (tac,udf,rt) <- command c begin -- $ modified
    return ([TAC.Label begin] ++ btac ++ [TAC.Label true] ++ tac ++ [TAC.Goto begin], udf, rt) -- $ modified
  AST.Assign i e -> do -- $ modified
    type1 <- lookup i False
    (tac,data_,type2) <- expressionInto (fixedVar i) e
    if isNothing type1
      then error $ "Variable " ++ i ++ " has not been declared."
    else if not $ endswith type2 (fromJust type1)
          then error $ "Assignment of an expression to Variable " ++ i
        ++ " not possible due to type conflict."
    else if not $ endswith "[]" (fromJust type1)
      then return (tac ++ if data_ == TAC.Variable (fromJust type1) then [] else [TAC.Copy (fromJust type1) data_], [], "")
    else do
      (t,l,env@(s:_),r,f,u,a) <- get
      let env' = insert i (show data_) env
      put (t,l,env',r,f,u,a)
      if isNothing $ Map.lookup i s
        then return (tac ++ [TAC.ArrayCopy (show data_) data_], [], "")
      else return (tac ++ if data_ == TAC.Variable (fromJust type1) || r /= "void" then [] else [TAC.ArrayCopy (fromJust type1) data_], [], "")
  AST.ToArray i e1 e2 -> do -- $ added
    type_ <- lookup i False
    if isNothing type_
          then error $ "Array " ++ i ++ " has not been declared."
    else if not $ endswith "]" $ fromJust type_
          then error $ "Name " ++ i ++ " does not denote an array."
        else do
      (tac1,data1,type1) <- expression e1
      if type1 /= "int"
        then error $ "Elements of array " ++ i ++ " only accessible via int indices."
      else do
        let signature = split ":" $ fromJust type_
        (tac2,data2,type2) <- expression e2
        if type2 /= (takeWhile (/= '[') $ last signature)
          then error $ "Assignment of an expression to array " ++ i ++ " not possible due to type conflict."
        else return (tac1 ++ tac2 ++ [TAC.ToArray (fromJust type_) data1 data2], [], "")
  AST.Declaration _type i -> do -- $$ added
    (t,l,s:ss,r,f,u,a) <- get
    let type_ = Map.lookup i s
    if isJust type_
      then error $ "Name " ++ i ++ " is already used."
    else do
      let (name, a') = newAlt i a
      put (t,l,(Map.insert i (name ++ ":" ++ show _type) s):ss,r,f,u,a')
      return ([], [], "")
  AST.ArrayDecl _type i -> do -- $$ added
    (t,l,s:ss,r,f,u,a) <- get
    let type_ = Map.lookup i s
    if isJust type_
      then error $ "Name " ++ i ++ " is already used."
    else do
      let (name, a') = newAlt i a
      put (t,l,(Map.insert i (name ++ ":" ++ show _type ++ "[]") s):ss,r,f,u,a')
      return ([], [], "")
  AST.ArrayAlloc _type e i -> do -- $$ added
    (t,l,s:ss,r,f,u,a) <- get
    let type_ = Map.lookup i s
    if isJust type_
      then error $ "Name " ++ i ++ " is already used."
    else do
      (tac,data_,type1) <- expression e
      if type1 /= "int"
        then error $ "Array " ++ i ++ "must be declared with int size."
      else do
        let type_ = case data_ of
              TAC.ImmediateInteger n | n > -1 -> show _type ++ "[]"
              TAC.Variable _ -> show _type ++ "[]"
              _ -> error $ "Array " ++ i ++ "must be declared with int size >= 0."
        let (name, a') = newAlt i a
        let signature = name ++ ":" ++ type_
        put (t,l,(Map.insert i signature s):ss,r,f,u,a')
        return (tac ++ [TAC.ArrayAlloc signature data_] ++ [TAC.Push $ TAC.Variable signature], [], "")
  AST.Environment c -> do -- $$ added
    (t,l,s,r,f,u,a) <- get
    put (t,l,Map.empty:s,r,Map.empty:f,u,a)
    (tac,udf,rt) <- command c next
    put (t,l,s,r,f,u,a)
    return (tac ++ (dealloc tac), udf, rt)
  AST.Function d p c -> do -- $$ added
    (t,l,s,r,f:ff,u,a) <- get
    let i = case d of
          AST.Declaration _type i -> i
          AST.ArrayDecl _type i -> i
    let signature = Map.lookup i f
    if isJust signature
          then error $ "User-defined function " ++ i ++ " already defined."
    else do
      let state = (0,0,[Map.empty],"",f:ff,u,Map.empty)
      let (f',u',udf) = function d p c state
      put (t,l,s,r,f',u',a)
      return ([], udf, "")

-- $| Generates three address code for one expression in the AST (possibly
-- generating code for subexpressions first) and determines its type.
expression :: AST.Expression -> State GenState (TAC.TAC,TAC.Data,Type)
expression = expressionInto newTemp

-- | Generates three address code for one expression in the AST (possibly
-- generating code for subexpressions first). The additional parameter will be
-- evaluated if code for something other than number or identifier is generated
-- and the returned variable will be used for the result.
-- $ Determines also its type.
expressionInto :: State GenState TAC.Variable -> AST.Expression
               -> State GenState (TAC.TAC,TAC.Data,Type) -- $ modified
expressionInto varFunc expr = case expr of
  AST.Calculation op e1 e2 -> do -- $ modified
    (tac1,data1,type1) <- expression e1
    (tac2,data2,type2) <- expression e2
    if endswith "]" type1 || endswith "]" type2
      then error "Cannot use an array as a whole in a calculation."
    else do
      let tacCommand1 = case op of
                T.Mod   -> \_ -> error "Modulo only applicable to Integers"
                T.Plus  -> TAC.FAdd
                T.Minus -> TAC.FSub
                T.Times -> TAC.FMul
                T.DivBy -> TAC.FDiv
      let tacCommand2 = case op of
                T.Mod   -> TAC.Mod
                T.Plus  -> TAC.Add
                T.Minus -> TAC.Sub
                T.Times -> TAC.Mul
                T.DivBy -> TAC.Div
      var2 <- newTemp
      let var2' = var2 ++ ":double"
      let (type_, tacCommand, coercion, data', data1', data2') = case (type1, type2) of
             ("int", "int")       -> ("int", tacCommand2, [], data1, data1, data2)
             ("double", "double") -> ("double", tacCommand1, [], data1, data1, data2)
             ("double", "int")        -> case data2 of
               TAC.Variable _ -> ("double", tacCommand1, [TAC.Convert var2' data'], data2, data1, TAC.Variable var2')
               _ -> ("double", tacCommand1, [], data1, data1, data2)
             ("int", "double")        -> case data1 of
               TAC.Variable _ -> ("double", tacCommand1, [TAC.Convert var2' data'], data1, TAC.Variable var2', data2)
               _ -> ("double", tacCommand1, [], data1, data1, data2)
      var1 <- varFunc
      type3 <- lookup var1 False
      let var1' = if isNothing type3 then var1 ++ ":" ++ type_ else fromJust type3
      return (tac1 ++ tac2 ++ coercion ++ [tacCommand var1' data1' data2'], TAC.Variable var1', type_)
  AST.Negate e -> do
    (tac,data_,type1) <- expression e -- $ modified
    if endswith "]" type1 -- $ added
      then error "Cannot use an array as a whole in a negation."
    else do
      var <- varFunc
      type2 <- lookup var False
      let var' = if isNothing type2 then var ++ ":" ++ type1 else fromJust type2
      return (tac ++ [if type1 == "double" then TAC.FNeg var' data_ else TAC.Neg var' data_], TAC.Variable var', type1) -- $ modified
  AST.Identifier i -> do -- $ modified
    type_ <- lookup i False
    if isNothing type_
          then error $ "Variable " ++ i ++ " has not been declared."
        else do
          let returnType = last $ split ":" $ fromJust type_
          return ([], TAC.Variable $ fromJust type_, returnType)
  AST.FromArray i e -> do -- $ added
    type1 <- lookup i False
    if isNothing type1
          then error $ "Array " ++ i ++ " has not been declared."
    else if not $ endswith "]" $ fromJust type1
          then error $ "Name " ++ i ++ " does not denote an array."
        else do
      (tac,data_,type2) <- expression e
      if type2 /= "int"
        then error $ "Elements of array " ++ i ++ " only accessible via int indices."
      else do
        let signature = split ":" $ fromJust type1
        var <- varFunc
        type3 <- lookup var False
        let returnType = (takeWhile (/= '[') $ last signature)
        let var' = if isNothing type3 then var ++ ":" ++ returnType else fromJust type3
        return (tac ++ [TAC.FromArray var' (fromJust type1) data_], TAC.Variable var', returnType)
  AST.Parameter e -> do -- $ added
    (tac,data_,type_) <- expression e
    return (tac ++ [TAC.Push data_], data_, type_)
  AST.Parameters e1 e2 -> do -- $ added
    (tac1,_,type1) <- expression e1
    (tac2,data_,type2) <- expression e2
    return (tac1 ++ tac2, data_, type1 ++ type2)
  AST.Func i p -> do -- $ added
    type_ <- lookup i True
    if isNothing type_
      then error $ "User-defined function " ++ i ++ " not in scope."
    else do
      (tac,_,params1) <- expression p
      let signature = split ":" $ fromJust type_
      let name = head signature
      let params2 = last signature
      if (name == "length_" && not(endswith "]" params2)) || (params1 /= params2 && name /= "length_")
          then error $ "User-defined function " ++ i ++ " call incompatible with given parameters."
      else do
          var <- varFunc
          type3 <- lookup var False
          let returnType = signature!!1
          let var' = if isNothing type3 || (endswith "]" $ fromJust type3) then var ++ ":" ++ returnType else fromJust type3
          return (tac ++ [TAC.Call var' $ head signature], TAC.Variable var', returnType)
  AST.Integer n -> return ([], TAC.ImmediateInteger n, "int")  -- $ modified
  AST.Double n -> return ([], TAC.ImmediateDouble n, "double") -- $ added
  AST.Character c -> return ([], TAC.ImmediateChar c, "char")

-- | Generates three address code for one boolean expression in the AST
-- (possibly generating code for boolean subexpressions first).
boolExpression :: AST.BoolExpression -> TAC.Label -> TAC.Label
               -> State GenState TAC.TAC
boolExpression bexpr lTrue lFalse = case bexpr of
  AST.LogOp op b1 b2 -> case op of
    T.And -> do
      b1True <- newLabel
      tac1 <- boolExpression b1 b1True lFalse
      tac2 <- boolExpression b2 lTrue lFalse
      return $ tac1 ++ [TAC.Label b1True] ++ tac2
    T.Or -> do
      b1False <- newLabel
      tac1 <- boolExpression b1 lTrue b1False
      tac2 <- boolExpression b2 lTrue lFalse
      return $ tac1 ++ [TAC.Label b1False] ++ tac2
  AST.Comparison op e1 e2 -> do
    (tac1,data1,type1) <- expression e1  -- $ modified
    (tac2,data2,type2) <- expression e2  -- $ modified
    if endswith "]" type1 || endswith "]" type2 -- $ added
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
      let jump = if type1 == "double" || type2 == "double" then jump1 else jump2
      return $ tac1 ++ tac2 ++ [jump lTrue] ++ [TAC.Goto lFalse]
  AST.Not b -> boolExpression b lFalse lTrue
  AST.Boolean b -> return [TAC.Goto (if b then lTrue else lFalse)]
  AST.Eof -> return [ TAC.GotoCond1 lTrue TAC.IsTrue (TAC.Variable "%eof%")
                    , TAC.Goto lFalse
                    ]

-- $| Given an abstract syntax tree for parameters and code each it generates an appendix with user-defined functions for later use.
function :: AST.Command -> AST.Command -> AST.AST -> GenState -> (FunctionScopes, UDFLabels, TACstream)
function d p c (t,l,s,_,f:ff,u,a) = (f':ff, u'', (name, intermediateCode'):_TACstream)
  where
      (f', r', i) = case d of
        AST.Declaration _type i -> (Map.insert i (r' ++ ":" ++ params p) f, name ++ ":" ++ show _type, i)
        AST.ArrayDecl _type i -> (Map.insert i (r' ++ ":" ++ params p) f, name ++ ":" ++ show _type ++ "[]", i)
      names = Map.lookup i u
      (name, u') = if isNothing names then (i ++ "_", Map.insert i [name] u) else (i ++ "_" ++ (show $ length $ fromJust names), Map.insert i ((fromJust names) ++ [name]) u)
      ((intermediateCode,_TACstream), (_,_,_,_,_,u'',_)) = runState (program $ AST.Sequence p c) (t,l,s,r',f':ff,u',a)          
      intermediateCode' = fst (allocateParameters p a) ++ [TAC.Call "dummy:double" "dummy"] ++ intermediateCode

-- $| Given a list of parameters it generates a string representing the signature.
params :: AST.Command -> String
params (AST.Sequence decls decl) = params decls ++ param decl
params decl = param decl

-- $| Given a parameter it generates a string representing the signature.
param :: AST.Command -> String
param (AST.Declaration _type _) = show _type
param (AST.ArrayDecl _type _) = show _type ++ "[]"

-- $| Generates three address code for a sequence of parameters in the AST.
allocateParameters :: AST.Command -> Locations -> (TAC.TAC, Locations)
allocateParameters params alts = case params of
  AST.Sequence p1 p2 -> (tac2 ++ tac1, alts2)
    where
    (tac1, alts1) = allocateParameters p1 alts
    (tac2, alts2) = allocateParameters p2 alts1
  AST.Declaration _type i -> let (name, alts') = newAlt i alts in ([TAC.Pop $ name ++ ":" ++ show _type], alts')
  AST.ArrayDecl _type i -> let (name, alts') = newAlt i alts in ([TAC.Pop $ name ++ ":" ++ show _type ++ "[]"], alts')


